/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
public import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.PhaseExt

namespace Lean.Compiler.LCNF

open ImpureType


/-!
The following section is the derived value analysis. It figures out parent values for variables that
were created using various forms of projections (currently `oproj` and `Array` accesses). This
information is later used to reduce reference counting pressure.
-/

/--
Contains information about values derived through various forms of projection from other values.
-/
structure DerivedValInfo where
  /--
  The variable this value was derived from. This is always set except for parameters as they have no
  value to be derived from.
  -/
  parent? : Option FVarId
  /--
  The set of variables that were derived from this value.
  -/
  children : FVarIdHashSet
  deriving Inhabited

abbrev DerivedValMap := Std.HashMap FVarId DerivedValInfo

namespace CollectDerivedValInfo

structure State where
  varMap : DerivedValMap := {}
  borrowedParams : FVarIdHashSet := {}

abbrev M := StateRefT State CompilerM

def visitParam (p : Param .impure) : M Unit :=
  modify fun s => { s with
    varMap := s.varMap.insert p.fvarId {
      parent? := none
      children := {}
    }
    borrowedParams :=
      if p.borrow && p.type.isPossibleRef then
        s.borrowedParams.insert p.fvarId
      else
        s.borrowedParams
  }

partial def addDerivedValue (parent : FVarId) (child : FVarId) : M Unit := do
  modify fun s => { s with
    varMap := s.varMap.modify parent fun info =>
      { info with children := info.children.insert child }
  }
  modify fun s => { s with
    varMap := s.varMap.insert child {
      parent? := some parent
      children := {}
    }
  }

partial def removeFromParent (child : FVarId) : M Unit := do
  if let (some parent) := (← get).varMap.get? child |>.bind (·.parent?) then
    modify fun s => { s with
      varMap := s.varMap.modify parent fun info =>
        { info with children := info.children.erase child }
    }

partial def collectCode (code : Code .impure) : M Unit := do
  match code with
  | .let decl k =>
    match decl.value with
    | .oproj _ parent =>
      addDerivedValue parent decl.fvarId
    | .fap ``Array.getInternal args =>
      if let .fvar parent := args[1]! then
        addDerivedValue parent decl.fvarId
    | .fap ``Array.get!Internal args =>
      if let .fvar parent := args[2]! then
        addDerivedValue parent decl.fvarId
    | .reset _ target =>
      removeFromParent target
    | _ => pure ()
    collectCode k
  | .jp decl k =>
    decl.params.forM visitParam
    collectCode decl.value
    collectCode k
  | .cases cases => cases.alts.forM (·.forCodeM collectCode)
  | .sset (k := k) .. | .uset (k := k) .. => collectCode k
  | .return .. | .jmp .. | .unreach .. => return ()

def collect (ps : Array (Param .impure)) (code : Code .impure) :
    CompilerM (DerivedValMap × FVarIdHashSet) := do
  let ⟨_, { varMap, borrowedParams }⟩ ← go |>.run {}
  return ⟨varMap, borrowedParams⟩
where
  go : M Unit := do
    ps.forM visitParam
    collectCode code

end CollectDerivedValInfo

structure VarInfo where
  isPossibleRef : Bool
  isDefiniteRef : Bool
  persistent : Bool
  deriving Inhabited

abbrev VarMap := FVarIdMap VarInfo

structure LiveVars where
  vars : FVarIdSet := {}
  borrows : FVarIdSet := {}
  deriving Inhabited

@[inline]
def LiveVars.merge (liveVars1 liveVars2 : LiveVars) : LiveVars :=
  let vars := liveVars1.vars.merge liveVars2.vars
  let borrows := liveVars1.borrows.merge liveVars2.borrows
  { vars, borrows }

@[inline]
def LiveVars.erase (liveVars : LiveVars) (fvarId : FVarId) : LiveVars :=
  let vars := liveVars.vars.erase fvarId
  let borrows := liveVars.borrows.erase fvarId
  { vars, borrows }

abbrev JPLiveVarMap := FVarIdMap LiveVars

structure Context where
  borrowedParams : FVarIdHashSet
  derivedValMap : DerivedValMap
  varMap : VarMap := {}
  jpLiveVarMap : JPLiveVarMap := {}

structure State where
  liveVars : LiveVars := {}

abbrev RcM := ReaderT Context <| StateRefT State CompilerM

@[inline]
def getVarInfo (fvarId : FVarId) : RcM VarInfo := return (← read).varMap.get! fvarId

@[inline]
def getJpLiveVars (fvarId : FVarId) : RcM LiveVars := return (← read).jpLiveVarMap.get! fvarId

@[inline]
def isLive (fvarId : FVarId) : RcM Bool := return (← get).liveVars.vars.contains fvarId

@[inline]
def isBorrowed (fvarId : FVarId) : RcM Bool := return (← get).liveVars.borrows.contains fvarId

@[inline]
def withParams (ps : Array (Param .impure)) (x : RcM α) : RcM α := do
  let update := fun ctx =>
    let varMap := ps.foldl (init := ctx.varMap) fun m p =>
      m.insert p.fvarId {
        isPossibleRef := p.type.isPossibleRef
        isDefiniteRef := p.type.isDefiniteRef
        persistent := false
      }
    { ctx with varMap := varMap }
  withReader update x

def LetValue.isPersistent (val : LetValue .impure) : Bool :=
  match val with
  | .fap _ xs => xs.isEmpty -- all global constants are persistent
  | _ => false

-- TODO: This heuristic should never be necessary
def refineTypeForExpr (value : LetValue .impure) (origt : Expr) : Expr := sorry

@[inline]
def withLetDecl (decl : LetDecl .impure) (x : RcM α) : RcM α := do
  let type := refineTypeForExpr decl.value decl.type
  let varInfo := {
    isPossibleRef := type.isPossibleRef
    isDefiniteRef := type.isDefiniteRef
    persistent := decl.value.isPersistent
  }
  withReader (fun ctx => { ctx with varMap := ctx.varMap.insert decl.fvarId varInfo}) do
    x

@[inline]
def withCtorAlt (discr : FVarId) (c : CtorInfo) (x : RcM α) : RcM α := do
  withReader
    (fun ctx =>
      { ctx with
        varMap :=
          match ctx.varMap.get? discr with
          | some info =>
            let isPossibleRef := c.type.isPossibleRef
            let isDefiniteRef := c.type.isDefiniteRef
            ctx.varMap.insert discr { info with isPossibleRef, isDefiniteRef }
          | none => ctx.varMap
      }) do x

def withLiveVars (liveVars : LiveVars) (x : RcM α) : RcM α := do
  let currentLiveVars := (← get).liveVars
  modify fun s => { s with liveVars }
  try
    x
  finally
    modify fun s => { s with liveVars := currentLiveVars }

@[inline]
def withCollectLiveVars (x : RcM α) : RcM (α × LiveVars) := do
  withLiveVars {} do
    let ret ← x
    return (ret, (← get).liveVars)

@[specialize]
partial def addDescendants (fvarId : FVarId) (shouldAdd : FVarId → Bool := fun _ => true) :
    RcM Unit := sorry

@[specialize]
def useVar (fvarId : FVarId) (shouldBorrow : FVarId → Bool := fun _ => true) : RcM Unit := do
  if !(← isLive fvarId) then
    let liveVars := (← get).liveVars
    addDescendants fvarId fun y =>
      !liveVars.vars.contains y && shouldBorrow y
  modify fun s => { s with liveVars := { s.liveVars with vars := s.liveVars.vars.insert fvarId }}

@[inline]
def useArg (args : Array (Arg .impure)) (arg : Arg .impure) : RcM Unit :=
  match arg with
  | .fvar fvarId =>
    useVar fvarId fun y =>
      args.all fun arg =>
        match arg with
        | .fvar z => y != z
        | .erased => true
  | .erased => return ()

def useArgs (args : Array (Arg .impure)) : RcM Unit := do
  args.forM (useArg args)

def useLetValue (value : LetValue .impure) : RcM Unit := do
  match value with
  | .oproj (var := fvarId) .. | .uproj (var := fvarId) .. | .sproj (var := fvarId) ..
  | .box (fvarId := fvarId) .. | .unbox (fvarId := fvarId) .. | .reset (var := fvarId) .. =>
    useVar fvarId
  | .ctor (args := args) .. | .fap (args := args) .. | .pap (args := args) .. =>
    useArgs args
  | .fvar fvarId args .. | .reuse (var := fvarId) (args := args) .. =>
    useVar fvarId
    useArgs args
  | .lit .. | .erased => return ()

@[inline]
def bindVar (fvarId : FVarId) : RcM Unit :=
  modify fun s => { s with liveVars := s.liveVars.erase fvarId }

def setRetLiveVars : RcM Unit := sorry

@[inline]
def addInc (fvarId : FVarId) (k : Code .impure) (n : Nat := 1) : RcM (Code .impure) := do
  let info ← getVarInfo fvarId
  if n == 0 then
    return k
  else
    sorry

@[inline]
def addDec (fvarId : FVarId) (k : Code .impure) : RcM (Code .impure) := do
  let info ← getVarInfo fvarId
  sorry

def addDecForAlt (altLiveVars : LiveVars) (k : Code .impure) : RcM (Code .impure) := do
  (← get).liveVars.vars.foldlM (init := k) fun k fvarId => do
    let info ← getVarInfo fvarId
    if !altLiveVars.vars.contains fvarId then
      if info.isPossibleRef && !(← isBorrowed fvarId) then
        addDec fvarId k
      else
        return k
    else if (← isBorrowed fvarId) && !altLiveVars.borrows.contains fvarId then
      addInc fvarId k
    else
      return k

def addIncBeforeConsumeAll (allArgs : Array (Arg .impure)) (k : Code .impure) :
    RcM (Code .impure) := do
  sorry

def addIncBefore (args : Array (Arg .impure)) (ps : Array (Param .impure)) (k : Code .impure) :
    RcM (Code .impure) := do
  sorry

def addDecAfterFullApp (args : Array (Arg .impure)) (ps : Array (Param .impure)) (k : Code .impure) :
    RcM (Code .impure) := do
  let mut k := k
  for h : i in 0...args.size do
    match args[i] with
    | .erased => pure ()
    | .fvar fvarId =>
      /-
      We must add a `dec` if `fvarId` must be consumed, it is alive after the application,
      and it has been borrowed by the application.
      Remark: `fvarId` may occur multiple times in the application (e.g., `f fvarId y fvarId`).
      This is why we check whether it is the first occurrence.
      -/
      let info ← getVarInfo fvarId
      if info.isPossibleRef && isFirstOcc args i && isBorrowParam arg args ps && !(← isLive fvarId) && (← isBorrowed fvarId) then
        k ← addDec fvarId k
  return k

/--
Add `dec` for `fvarId` if `fvarId` is a reference, not alive in `k` and not borrowed.
-/
def addDecIfNeeded (fvarId : FVarId) (k : Code .impure) : RcM (Code .impure) := do
  let info ← getVarInfo fvarId
  if info.isPossibleRef && !(← isBorrowed fvarId) && !(← isLive fvarId) then
    addDec fvarId k
  else
    return k

/--
Add `dec` instructions for parameters that are references, are not alive in `k`, and are not borrow.
That is, we must make sure these parameters are consumed.
-/
def addDecForDeadParams (ps : Array (Param .impure)) (k : Code .impure) : RcM (Code .impure) :=
  ps.foldlM (init := k) fun k p => do
    let k ← addDecIfNeeded p.fvarId k
    bindVar p.fvarId
    return k

def LetDecl.explicitRc (code : Code .impure) (decl : LetDecl .impure) (k : Code .impure) :
    RcM (Code .impure) := do
  /-
  `decl.fvarId` can be unused in `k` so we might have to drop it. Note that we do not remove the let
  because we are in the impure phase of the compiler so `decl.value` can have side effects that we
  don't want to loose.
  -/
  let k ← addDecIfNeeded decl.fvarId k
  let k ←
    match decl.value with
    | .ctor (args := args) .. | .reuse (args := args) .. | .pap (args := args) .. =>
      addIncBeforeConsumeAll args (code.updateLet! decl k)
    | .oproj (var := fvarId) .. =>
      let k ← addDecIfNeeded fvarId k
      let k ← if ← isBorrowed decl.fvarId then pure k else addInc decl.fvarId k
      return code.updateLet! decl k
    | .uproj (var := fvarId) .. | .sproj (var := fvarId) .. | .unbox (fvarId := fvarId) .. =>
      let k ← addDecIfNeeded fvarId k
      pure <| code.updateLet! decl k
    | .fap f args =>
      let ps := (← getImpureSignature? f).get!.params
      let k ← addDecAfterFullApp args ps k
      let liveVars := (← get).liveVars
      let value ←
        if f == ``Array.getInternal && (← isBorrowed decl.fvarId) then
          pure <| .fap ``Array.getInternalBorrowed args
        else if f == ``Array.get!Internal && (← isBorrowed decl.fvarId) then
          pure <| .fap ``Array.get!InternalBorrowed args
        else
          pure <| decl.value
      let decl ← decl.updateValue value
      let k := code.updateLet! decl k
      addIncBefore args ps k
    | .fvar fvarId args =>
      let allArgs := args.push <| .fvar fvarId
      addIncBeforeConsumeAll allArgs (code.updateLet! decl k)
    | .lit .. | .box .. | .reset .. | .erased .. =>
      pure <| code.updateLet! decl k
  useLetValue decl.value
  bindVar decl.fvarId
  return k

partial def Code.explicitRc (code : Code .impure) : RcM (Code .impure) := do
  match code with
  | .let decl k =>
    withLetDecl decl do
      let k ← k.explicitRc
      decl.explicitRc code k
  | .jp decl k =>
    let (decl, jpLive) ←
      withParams decl.params do
      withCollectLiveVars do
        let value ← decl.value.explicitRc
        let value ← addDecForDeadParams decl.params value
        decl.updateValue value
    withReader (fun ctx => { ctx with jpLiveVarMap := ctx.jpLiveVarMap.insert decl.fvarId jpLive }) do
      let k ← k.explicitRc
      return code.updateFun! decl k
  | .cases cs =>
    let alts ← cs.alts.mapM fun alt =>
      match alt with
      | .ctorAlt c k =>
        withCtorAlt cs.discr c do
        withCollectLiveVars do
          let k ← k.explicitRc
          return alt.updateCode k
      | .default k =>
        withCollectLiveVars do
          let k ← k.explicitRc
          return alt.updateCode k
    let caseLiveVars := alts.foldl (init := {}) fun acc ⟨_, altLive⟩ => acc.merge altLive
    withLiveVars caseLiveVars do
      useVar cs.discr
      let alts ← alts.mapM fun ⟨alt, altLiveVars⟩ => do
        match alt with
        | .ctorAlt c k =>
          withCtorAlt cs.discr c do
            let k ← addDecForAlt altLiveVars k
            return alt.updateCode k
        | .default k =>
          let k ← addDecForAlt altLiveVars k
          return alt.updateCode k
      return code.updateAlts! alts
  | .jmp fvarId args =>
    let jpLiveVars ← getJpLiveVars fvarId
    let ps := (← findFunDecl? fvarId).get!.params
    withLiveVars jpLiveVars do
      let code ← addIncBefore args ps code
      useArgs args
      return code
  | .return fvarId =>
    setRetLiveVars
    let info ← getVarInfo fvarId
    useVar fvarId
    if info.isPossibleRef && (← isBorrowed fvarId) then
      addInc fvarId code
    else
      return code
  | .uset (var := var) (k := k) .. | .sset (var := var) (k := k) .. =>
    let k ← k.explicitRc
    -- We don't need to insert `y` since we only need to track live variables that are references at runtime
    useVar var
    return code.updateCont! k
  | .unreach .. =>
    setRetLiveVars
    return code

def Decl.explicitRc (decl : Decl .impure) : CompilerM (Decl .impure) := do
  let value ← decl.value.mapCodeM fun code => do
    let ⟨derivedValMap, borrowedParams⟩ ← CollectDerivedValInfo.collect decl.params code
    go code |>.run {
      borrowedParams,
      derivedValMap,
    } |>.run' {}
  return { decl with value }
where
  go (code : Code .impure) : RcM (Code .impure) := do
    withParams decl.params do
      let code ← code.explicitRc
      addDecForDeadParams decl.params code

public def explicitRc : Pass :=
  Pass.mkPerDeclaration `explicitRc .impure Decl.explicitRc 0

builtin_initialize
  registerTraceClass `Compiler.explicitRc (inherited := true)

end Lean.Compiler.LCNF
