import Lean.Compiler.ExternAttr
import Lean.Compiler.IR
import Lean.Compiler.LCNF.PhaseExt

namespace Lean.Compiler.LCNF


-- paraphrased from https://github.com/leanprover/lean4/blob/cbf1b433d7dcc75ce6a2e5aab320385bf5e47c82/src/library/compiler/llnf.cpp#L257
def _root_.Lean.IR.CtorInfo.ofCtorName (ctorName : Name) : CoreM IR.CtorInfo := do
  let env ← getEnv
  let some (.ctorInfo ctorVal) := env.find? ctorName | unreachable!
  let ((size, usize, ssize), _) ← (Meta.forallTelescopeReducing ctorVal.type processType).run
  -- TODO: actual values
  return {
    name := ctorName
    cidx := ctorVal.cidx
    size := size
    usize := usize
    ssize := ssize
  }
where
  -- TODO: the C++ implementation is more nuanced
  isIrrelevant (paramTyp : Expr) : MetaM Bool := do
    return paramTyp.isSort || (← Meta.inferType paramTyp).isProp

  isBuiltInScalar (paramTypName : Name) : MetaM (Option Nat) := do
    let builtinScalars := #[
      (``UInt8, 1), (``UInt16, 2), (``UInt32, 4), (``UInt64, 8),
      (``Float, 8)
    ]
    for (name, size) in builtinScalars do
      if paramTypName == name then
        return some size
    return none

  isEnumTyp (paramTypName : Name) : MetaM (Option Nat) := do
    let env ← getEnv
    let some (.inductInfo inductVal) := env.find? paramTypName | return none
    let ctors := inductVal.ctors
    let ctorCount := ctors.length
    if ctorCount == 1 then
      return none
    for ctor in ctors do
      let some (.ctorInfo ctorVal) := env.find? ctor | unreachable!
      if ctorVal.type.isForall then
        return none
    if ctorCount < 2^8 then
      return some 1
    else if ctorCount < 2^16 then
      return some 2
    else
      return some 4

  isScalar (paramTyp : Expr) : MetaM (Option Nat) := do
    let .some paramTypName := paramTyp.getAppFn.constName? | return none
    isBuiltInScalar paramTypName <|> isEnumTyp paramTypName

  processType (params : Array Expr) (_res : Expr) : MetaM (Nat × Nat × Nat) := do
    let mut size := 0
    let mut usize := 0
    let mut ssize := 0
    for param in params do
      let paramTyp ← Meta.inferType param
      -- irrelevant types
      if ← isIrrelevant paramTyp then
        pure ()
      -- usize parameter
      else if param.constName? == some `USize then
        usize := usize + 1
      else if let some paramSize ← isScalar param then
        ssize := ssize + paramSize
      -- object parameters
      else
        size := size + 1
    return (size, usize, ssize)

-- paraphrased from https://github.com/leanprover/lean4/blob/cbf1b433d7dcc75ce6a2e5aab320385bf5e47c82/src/library/compiler/ir.cpp#L108-L131
def _root_.Lean.Expr.toIRType (e : Expr) : CompilerM IR.IRType :=
  match e with
  | .const name .. =>
    match name with
    | ``UInt8 => return .uint8
    | ``UInt16 => return .uint16
    | ``UInt32 => return .uint32
    | ``UInt64 => return .uint64
    | ``USize => return .usize
    | ``Float => return .float
    -- TODO: we can generate better types here
    | _ => return .tobject
  | .forallE .. => return .tobject
  | .app .. => return .tobject
  | _ => throwError s!"IR unsupported type {e.dbgToString}"

inductive FVarTranslation where
| translation (idx : Nat)
/- The IR does not have a concept of erased as the value of a let binder
so if these let binders do occur we cannot translate them but instead
have to insert an erased declaration explicitly at the target location. -/
| erased
deriving Inhabited

structure State where
  counter : Nat := 0
  fvarMap : FVarIdMap FVarTranslation := {}

abbrev IrM := StateRefT State CompilerM

def getId : IrM Nat := do
  let currId := (← get).counter
  modify fun s => { s with counter := currId + 1 }
  return currId

def mkFVar (fvarId : FVarId) : IrM Nat := do
  let newIdent ← getId
  modify fun s => { s with fvarMap := s.fvarMap.insert fvarId (.translation newIdent) }
  return newIdent

def mkErasedFVar (fvarId : FVarId) : IrM Unit := do
  modify fun s => { s with fvarMap := s.fvarMap.insert fvarId .erased }

def mkVarId (fvarId : FVarId) : IrM IR.VarId := do
  return { idx := (← mkFVar fvarId) }

def mkJoinPointId (fvarId : FVarId) : IrM IR.JoinPointId := do
  return { idx := (← mkFVar fvarId) }

def Param.toIRParam (param : Param) : IrM IR.Param := do
  return {
    x := (← mkVarId param.fvarId)
    borrow := param.borrow
    ty := (← param.type.toIRType)
  }

def translateFVar! (fvarId : FVarId) : IrM FVarTranslation := do
  return (← get).fvarMap.find! fvarId

def translateArg! (arg : Arg) : IrM IR.Arg := do
  match arg with
  | .erased => return .irrelevant
  | .fvar fvarId =>
    match (← translateFVar! fvarId) with
    | .translation idx => return .var { idx }
    | .erased => return .irrelevant
  | .type .. => return .irrelevant

def translateLetValue! (value : LetValue) : IrM (Option IR.Expr) := do
  match value with
  | .value lit =>
    let irLit := match lit with
    | .natVal val => .num val
    | .strVal val => .str val
    return some <| .lit irLit
  | .erased => return none
  | .proj _ idx struct =>
    match (← translateFVar! struct) with
    | .translation varIdx => return some <| .proj idx { idx := varIdx }
    | .erased => return none
  | .const declName _ args =>
    let translatedArgs ← args.mapM translateArg!
    let env ← getEnv
    match (← getDeclAt? declName .mono) <|> (← getDeclAt? declName .base) with
    | some decl =>
      if decl.getArity == args.size then
        return some <| .fap declName translatedArgs
      else
        return some <| .pap declName translatedArgs
    | none =>
      match env.find? declName with
      | some (.ctorInfo info) =>
        let args := args[info.numParams:].toArray
        if info.numFields == args.size then
          return some <| .ctor (← IR.CtorInfo.ofCtorName declName) translatedArgs
        else
          throwError "Tried to translate a pap ctor, this is a bug"
      | some (.opaqueInfo _) | some (.defnInfo _) => externApplication declName translatedArgs
      | some (.quotInfo info) =>
        match info.kind with
        | .type => throwError "Tried to translate Quot.type"
        -- TODO: same hack as Quot.lcInv
        -- Here i might have to be careful with types though
        | .ctor => return some <| .fap ``id #[(← translateArg! args[2]!)]
        | .lift => throwError "Tried to translate Quot.lift"
        | .ind => throwError "Tried to translate Quot.ind"
      | some (.axiomInfo info) =>
        match info.name with
        -- TODO: the id is a little hack here, in general the idea is
        -- if we see Quot.lcInv we want to return the 3rd argument here
        -- but the low level IR doesn't have a concept of assigning an fvar to a variable
        | ``Quot.lcInv => return some <| .fap ``id #[(← translateArg! args[2]!)]
        | name => throwError s!"Tried to translate axiom without code: {name}"
      | _ => throwError s!"Tried to translate a recursor, inductive or theorem: {declName}"
  | .fvar fvarId args =>
    match (← translateFVar! fvarId) with
    | .translation varIdx => return some <| .ap { idx := varIdx } (← args.mapM translateArg!)
    | .erased => return none
where
  externApplication (declName : Name) (args : Array IR.Arg) : IrM (Option IR.Expr) := do
    -- getExternConstArity will fall back onto the non IR arity if no extern data is present
    let arity ← getExternConstArity declName
    if arity == args.size then
      return some <| .fap declName args
    else
      return some <| .pap declName args

partial def Code.toFnBody (code : Code) : IrM IR.FnBody := do
  match code with
  | .let decl k =>
    if let some value ← translateLetValue! decl.value then
      let varId ← mkVarId decl.fvarId
      let type ← decl.type.toIRType
      let continuation ← toFnBody k
      return .vdecl varId type value continuation
    else
      mkErasedFVar decl.fvarId
      let continuation ← toFnBody k
      return continuation
  | .jp decl k =>
    let jpId ← mkJoinPointId decl.fvarId
    let params ← decl.params.mapM Param.toIRParam
    let jpBody ← toFnBody decl.value
    let continuation ← toFnBody k
    return .jdecl jpId params jpBody continuation
  | .jmp fvarId args =>
    let .translation idx ← translateFVar! fvarId | throwError "Tried to translate non existing join point to IR"
    return .jmp { idx } (← args.mapM translateArg!)
  | .cases cs =>
    let .translation discrVarIdx ← translateFVar! cs.discr | throwError "cases on erased"
    let discrType ← do
      if let some discrDecl ← findLetDecl? cs.discr then
        pure discrDecl.type
      else if let some param ← findParam? cs.discr then
        pure param.type
      else
        unreachable!
    let discrIRType ← discrType.toIRType
    let discrVarId := { idx := discrVarIdx }
    return .case cs.typeName discrVarId discrIRType (← cs.alts.mapM (goAlt discrVarId))
  | .return fvarId =>
    match (← translateFVar! fvarId) with
    | .translation varIdx => return .ret <| .var { idx := varIdx }
    | .erased => return .ret .irrelevant
  | .unreach .. => return .unreachable
  -- At this point lambda lifting happend so no local functions are left.
  | .fun .. => unreachable!
where
  goAlt (discr : IR.VarId) (alt : Alt) : IrM IR.Alt := do
    match alt with
    | .alt ctorName params code =>
      let processParam idx param := do
        let paramVarId ← mkVarId param.fvarId
        let paramTyp ← param.type.toIRType
        let expr := .proj idx.val discr
        pure (paramVarId, paramTyp, expr)
      let paramsInfo ← params.mapIdxM processParam
      let mut body ← toFnBody code
      for (paramVarId, paramTyp, expr) in paramsInfo do
        body := .vdecl paramVarId paramTyp expr body
      return .ctor (← IR.CtorInfo.ofCtorName ctorName) body
    | .default code => return .default (← toFnBody code)

/- TODO: What about extern decls? 
They are not available here anymore, we have to generate the info at
the compiler frontend.
-/
def Decl.toIRDecls (decls : Array Decl) : CompilerM (Array IR.Decl) := do
  decls.mapM go |>.run' {}
where
  go (decl : Decl) : IrM IR.Decl := do
    let params ← decl.params.mapM Param.toIRParam
    let type ← decl.type.toIRType
    let body ← decl.value.toFnBody
    /- TODO: sorryDep? is already implemented for IR.Decl but needs
      to run in the IR.CompilerM monad, once we switched into that one
      we will first run updateSorryDep on them.
    -/
    return .fdecl decl.name params type body {}

def Decl.externToIRDecls (externs : Array Decl) : CompilerM (Array IR.Decl) :=
  externs.mapM go |>.run' {}
where
  go (decl : Decl) : IrM IR.Decl := do
    let params ← decl.params.mapM Param.toIRParam
    let type ← decl.type.toIRType
    return .extern decl.name params type (getExternAttrData? (← getEnv) decl.name).get!

end Lean.Compiler.LCNF
