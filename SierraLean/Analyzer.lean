import SierraLean.Parser
import SierraLean.FuncData
import Lean.Meta.SynthInstance
import Lean.Meta.AppBuilder
import Qq

open Lean Qq Lean.Expr

namespace Sierra

def getTypeRefs (f : SierraFile) : HashMap Identifier Identifier := HashMap.ofList f.typedefs

def getLibfuncRefs (f : SierraFile) : HashMap Identifier Identifier := HashMap.ofList f.libfuncs

def RefTable.getOrMkNew (refs : RefTable) (n : ℕ) : MetaM (RefTable × FVarId) :=
  match refs.find? n with
  | .some x => return (refs, x)
  | _ => do
    let fv ← mkFreshFVarId
    return (refs.insert n fv, fv)

structure State where
  (refs : HashMap Nat FVarId)
  (types : HashMap Nat Expr)
  (conditions : List Expr)
  (pc : Nat)

abbrev M := StateT State MetaM

def statementStep (f : SierraFile) : M Unit := do
  let types := getTypeRefs f
  let libfuncs := getLibfuncRefs f
  let ⟨refs, types, conditions, pc⟩ ← get
  let ⟨i, inputs, outputs⟩ := f.statements.get! pc
  let i' := libfuncs.find! i
  match i' with 
  | (.name istr []) =>
    let fd : Expr := mkConst ("Sierra" ++ "FuncData" ++ istr)  -- TODO add parameters
    let fd_condition : Expr ← Meta.mkProjection fd `condition  -- The plain condition
    let mut refs := refs
    let mut input_exprs := []
    let mut output_exprs := []
    for n in inputs do
      let (refs', fv) ← RefTable.getOrMkNew refs n
      refs := refs'
      input_exprs := input_exprs ++ [Expr.fvar fv]
    for n in outputs do
      let (refs', fv) ← RefTable.getOrMkNew refs n
      refs := refs'
      output_exprs := output_exprs ++ [Expr.fvar fv]
    let fd_condition := mkAppN fd_condition (input_exprs ++ output_exprs).toArray
    let conditions' := conditions ++ [fd_condition]
    let fd : FuncData i' := FuncData_register i'
    let pc' := fd.pcChange pc
    set (⟨refs, types, conditions', pc'⟩ : State)
    return
  | _ => return

def sf : SierraFile :=
{ typedefs := [(Identifier.ref 0, Identifier.name "felt252" [])],
  libfuncs := [(Identifier.ref 0, Identifier.name "felt252_add" [])],
  statements := [(Identifier.ref 0, [0, 1], [2]), (Identifier.ref 0, [1, 2], [3]), (Identifier.name "return" [], [2], [])],
  declarations := [(Identifier.ref 0, 0, [(0, Identifier.ref 0), (1, Identifier.ref 0)], [Identifier.ref 2])] }

def statementStepAndReturn (f : SierraFile) : MetaM (List Expr) := do
  let (_, state) ← StateT.run (statementStep f) ⟨HashMap.empty, HashMap.empty, [], 0⟩
  let (_, state) ← StateT.run (statementStep f) state
  return state.conditions

#check @Sierra.FuncData.condition
#eval statementStepAndReturn sf 
