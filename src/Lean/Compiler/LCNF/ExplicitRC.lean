/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Compiler.LCNF.CompilerM
public import Lean.Compiler.LCNF.PassManager

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

def withLiveVars (liveVars : LiveVars) (x : RcM α) : RcM α := do
  let currentLiveVars := (← get).liveVars
  modify fun s => { s with liveVars }
  try
    x
  finally
    modify fun s => { s with liveVars := currentLiveVars }

@[specialize]
def useVar (fvarId : FVarId) (shouldBorrow : FVarId → Bool := fun _ => true) : RcM Unit := sorry

def useArgs (args : Array (Arg .impure)) : RcM Unit := sorry

def setRetLiveVars : RcM Unit := sorry

def addDecForDeadParams (ps : Array (Param .impure)) (code : Code .impure) : RcM (Code .impure) :=
  sorry

@[inline]
def addInc (fvarId : FVarId) (k : Code .impure) (n : Nat := 1) : RcM (Code .impure) :=
  sorry

def addIncBefore (args : Array (Arg .impure)) (ps : Array (Param .impure)) (k : Code .impure) :
    RcM (Code .impure) := do
  sorry

def LetDecl.explicitRc (code : Code .impure) (decl : LetDecl .impure) (k : Code .impure) :
    RcM (Code .impure) := do
  sorry

partial def Code.explicitRc (code : Code .impure) : RcM (Code .impure) := do
  match code with
  | .let decl k =>
    withLetDecl decl do
      let k ← k.explicitRc
      decl.explicitRc code k
  | .jp decl k =>
    let (decl, jpLive) ←
      withParams decl.params do
      withLiveVars {} do
        let value ← decl.value.explicitRc
        let value ← addDecForDeadParams decl.params value
        let decl ← decl.updateValue value
        return (decl, (← get).liveVars)
    withReader (fun ctx => { ctx with jpLiveVarMap := ctx.jpLiveVarMap.insert decl.fvarId jpLive }) do
      let k ← k.explicitRc
      return code.updateFun! decl k
  | .cases cs =>
    let alts : Array (Alt .impure × LiveVars) ← cs.alts.mapM fun alt =>
      sorry
    let caseLiveVars : LiveVars := alts.foldl (init := {}) fun acc ⟨_, altLive⟩ => acc.merge altLive
    let alts : Array (Alt .impure) ← alts.mapM fun ⟨alt, altLiveVars⟩ =>
      sorry
    sorry
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
    if info.isPossibleRef && (← get).liveVars.borrows.contains fvarId then
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
