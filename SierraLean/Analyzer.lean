import SierraLean.Parser
import SierraLean.FuncData
import Lean.Meta.SynthInstance
import Lean.Meta.AppBuilder
import Lean.Meta.Basic
import Qq

open Lean Qq Expr Meta Sierra

namespace Sierra

def getTypeRefs (f : SierraFile) : HashMap Identifier Identifier := HashMap.ofList f.typedefs

def getLibfuncRefs (f : SierraFile) : HashMap Identifier Identifier := HashMap.ofList f.libfuncs

structure State where
  (conditions : List Expr)
  (pc : Nat)

abbrev M := StateT State MetaM

def withGetOrMkNewRef (refs : RefTable) (n : ℕ) (type : Expr) 
    (k : RefTable → FVarId → M α) : M α :=
  match refs.find? n with
  | .some x => k refs x
  | _ => do
    withLocalDeclD ("ref" ++ n.repr : String) type fun e =>
      let fv := e.fvarId!
      k (refs.insert n fv) fv

def withGetOrMkNewRefs (refs : RefTable) (ns : List ℕ) (types : List Expr) (fvs : List FVarId := [])
    (k : RefTable → List FVarId → M α) [Inhabited (M α) ]: M α :=
  match ns, types with
  | (n :: ns), (t :: ts) => withGetOrMkNewRef refs n t fun refs' fv =>
                              withGetOrMkNewRefs refs' ns ts (fv :: fvs) k
  | [],        []        => k refs fvs
  | _,         _         => panic "types and ref list not the same length!"

def Expr.mkAnds : List Expr → Expr
| []        => mkConst ``True
| [e]       => e
| (e :: es) => mkApp (mkApp (mkConst ``And) e) (mkAnds es)

def mkExistsFVars (fvs : List Expr) (e : Expr) : M Expr :=
  match fvs with
  | []        => return e
  | fv :: fvs => do mkAppM ``Exists #[← mkLambdaFVars #[fv] <| ← mkExistsFVars fvs e]

def withStatementStep (f : SierraFile) (refs : RefTable) 
    (k : RefTable → List FVarId → M α) [Inhabited (M α)] : M α := do
  let libfuncs := getLibfuncRefs f
  let ⟨conditions, pc⟩ ← get
  let ⟨i, inputs, outputs⟩ := f.statements.get! pc
  let i' := libfuncs.find! i
  match i' with 
  | (.name istr []) =>
    let fd : Expr := mkConst ("Sierra" ++ "FuncData" ++ istr)  -- TODO add parameters
    let fd_condition : Expr ← Meta.mkProjection fd `condition  -- The plain condition
    let fd_inputTypes : Expr ← Meta.mkProjection fd `inputTypes
    let fd_outputTypes : Expr ← Meta.mkProjection fd `outputTypes
    let fd_types : Expr ← mkAppM `List.append #[fd_inputTypes, fd_outputTypes]
    let mut fd_typeList : List Expr := []
    for i in [:(inputs.length+outputs.length)] do
      fd_typeList := fd_typeList ++ [← mkAppM `List.get! #[fd_types, .lit <| .natVal i]]
    withGetOrMkNewRefs refs (inputs ++ outputs) fd_typeList [] fun refs fvs => do
      let fves := fvs.map Expr.fvar
      let fd_condition := mkAppN fd_condition fves.toArray
      let conditions' := conditions ++ [fd_condition]
      let fd : FuncData i' := FuncData_register i'
      let pc' := fd.pcChange pc
      set (⟨conditions', pc'⟩ : State)
      k refs fvs
  | _ => k refs []

partial def statementLoop (f : SierraFile) (finputs : List (Nat × Identifier))
    (refs : RefTable := HashMap.empty) : M Expr := do
  let ⟨conditions, pc⟩ ← get
  let ⟨i, _, _⟩ := f.statements.get! pc
  match i with
  | .name "return" [] =>
    let e := Expr.mkAnds conditions
    let (intermediateRefs, ioRefs) := refs.toList.partition fun (n, _) => n ∉ finputs.map Prod.fst
    let e ← mkExistsFVars (intermediateRefs.map (fun (_, fv) => .fvar fv)) e
    let e ← mkLambdaFVars (ioRefs.map (fun (_, fv) => .fvar fv)).toArray e
    return e
  | _ =>
    withStatementStep f refs fun refs _ =>
      statementLoop f finputs refs

def sf : SierraFile :=
{ typedefs := [(Identifier.ref 0, Identifier.name "felt252" [])],
  libfuncs := [(Identifier.ref 0, Identifier.name "felt252_add" [])],
  statements := [(Identifier.ref 0, [0, 1], [2]), (Identifier.ref 0, [1, 2], [3]), (Identifier.name "return" [], [2], [])],
  declarations := [(Identifier.ref 0, 0, [(0, Identifier.ref 0), (1, Identifier.ref 0)], [Identifier.ref 2])] }

def statementLoopAndReturn (f : SierraFile) : MetaM Format := do
  let e ← StateT.run (statementLoop f [(0, Identifier.ref 0), (1, Identifier.ref 0)]) ⟨[], 0⟩
  ppExpr e.1

#check (1 ∈ [1, 2])
#eval statementLoopAndReturn sf

