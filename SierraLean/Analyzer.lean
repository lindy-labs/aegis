import SierraLean.Parser
import SierraLean.FuncData
import Lean.Meta.AppBuilder

open Lean Expr Meta Sierra

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
    let name ← mkFreshUserName ("ref" ++ n.repr : String)
    withLocalDeclD name type fun e =>
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
  let types := getTypeRefs f
  let libfuncs := getLibfuncRefs f
  let ⟨conditions, pc⟩ ← get
  let .some s := f.statements.get? pc
    | throwError "Program counter out of bounds"
  let .some i' := libfuncs.find? s.libfunc_id
    | throwError "Could not find function in declared libfuncs"  -- TODO catch control flow commands before this
  match i' with 
  | .name istr params =>
    let mut fd := mkConst ("Sierra" ++ "FuncData" ++ istr)
    for p in params do
      match p with
      | .const n => fd := mkApp fd <| .lit <| .natVal n
      | .identifier t => 
          let .some t' := types.find? t
            | throwError "Could not find referenced type"
          fd := mkApp fd <| Type_register t'
      | _ => fd := fd  -- TODO
    let fd_condition ← Meta.mkProjection fd `condition  -- The plain condition
    let fd_inputTypes ← Meta.mkProjection fd `inputTypes
    let fd_outputTypes ← Meta.mkProjection fd `outputTypes
    let fd_types ← mkAppM `List.append #[fd_inputTypes, fd_outputTypes]
    let mut fd_typeList : List Expr := []
    let inputs := s.args
    let outputs := (s.branches.map BranchInfo.results).join
    for i in [:(inputs.length+outputs.length)] do
      fd_typeList := fd_typeList ++ [← mkAppM `List.get! #[fd_types, .lit <| .natVal i]]
    withGetOrMkNewRefs refs (inputs ++ outputs).reverse fd_typeList.reverse [] fun refs fvs => do
      let fd_condition ← whnf <| mkAppN fd_condition (fvs.map Expr.fvar).toArray
      -- Only add new condition if it is not trivial
      let conditions' := if ← isDefEq fd_condition (mkConst ``True) then conditions
                         else conditions ++ [fd_condition]
      let fd : FuncData i' := FuncData_register i'
      let pc' := fd.pcChange pc
      let refs' := fd.refsChange refs (inputs ++ outputs)
      set (⟨conditions', pc'⟩ : State)
      k refs' fvs
  | _ => throwError "Resolved libfunc does not have name"

partial def statementLoop (f : SierraFile) (finputs : List (Nat × Identifier))
    (refs : RefTable := HashMap.empty) (gas : ℕ := 25) : M Expr := do
  let ⟨conditions, pc⟩ ← get
  let ⟨i, sinputs, _⟩ := f.statements.get! pc  -- `sinputs` are the returned cells
  if gas = 0 then return Expr.mkAnds conditions
  match i with
  | .name "return" [] =>
    -- Filter out conditions refering to "dangling" FVars (mostly due to `drop()`)
    let conditions := conditions.filter (¬ ·.hasAnyFVar (¬ (refs.toList.map (·.2)).contains ·))
    logInfo "{refs.toList}"
    -- Take the conjunction of all remaining conditions
    let e := Expr.mkAnds conditions
    let (ioRefs, intRefs) := refs.toList.reverse.partition (·.1 ∈ finputs.map (·.1) ++ sinputs)
    -- Existentially close over intermediate references
    let e ← mkExistsFVars (intRefs.map (.fvar ·.2)) e
    -- Lambda-close over input and output references
    let e ← mkLambdaFVars (ioRefs.map (.fvar ·.2)).toArray e
    return e
  | _ =>
    -- Process next statement
    withStatementStep f refs fun refs _ => statementLoop f finputs refs (gas - 1)

def analyzeFile (s : String) : MetaM Format := do
  match parseGrammar s with
  | .ok sf =>
    let ⟨_, pc, inputArgs, _⟩ := sf.declarations.get! 0  -- TODO Don't we need the output types?
    let e ← StateT.run (statementLoop sf inputArgs) ⟨[], pc⟩
    ppExpr e.1
  | .error str => throwError "Could not parse input file:\n{str}"

def code' :=
"type [0] = felt252;

libfunc [0] = felt252_add;
libfunc [1] = dup<[0]>;

[1]([0]) -> ([0], [1]);
[0]([0], [1]) -> ([2]);
[0]([0], [2]) -> ([3]);
return([3]);

[0]@0([0]: [0]) -> ([0]);"

#eval analyzeFile code'

#check Expr.containsFVar
