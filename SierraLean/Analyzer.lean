import SierraLean.Parser
import SierraLean.FuncData
import Lean.Meta.AppBuilder

open Lean Expr Meta Sierra

namespace Sierra

def getTypeRefs (f : SierraFile) : HashMap Identifier Identifier := HashMap.ofList f.typedefs

def getLibfuncRefs (f : SierraFile) : HashMap Identifier Identifier := HashMap.ofList f.libfuncs

/-- A tree to contain expressions to be composed with `And` and `Or`.
If we want to avoid trees, this has to be replaced by some graph structure in the future. -/
inductive AndOrTree 
| nil  : AndOrTree
| cons : Expr → List AndOrTree → AndOrTree

-- TODO delete
def Expr.mkAnds : List Expr → Expr
| []        => mkConst ``True
| [e]       => e
| (e :: es) => mkApp (mkApp (mkConst ``And) e) (mkAnds es)

/-- Build the disjunction of a list of expressions -/
def Expr.mkOrs : List Expr → Expr
| []        => mkConst ``False
| [e]       => e
| (e :: es) => mkApp (mkApp (mkConst ``Or) e) <| mkOrs es

/-- Compile an `AndOrTree` down to a single expression -/
partial def AndOrTree.toExpr : AndOrTree → Expr
| nil       => mkConst ``True
| cons e [] => e
| cons e ts => mkApp (mkApp (mkConst ``And) e) <| Expr.mkOrs <| (AndOrTree.toExpr <$> ts)

/-- Filter an `AndOrTree` by a boolean predicate on expressions -/
partial def AndOrTree.filter (p : Expr → Bool) : AndOrTree → AndOrTree
| nil                     => nil
| cons e []               => if p e then cons e [] else nil
| cons e [c@(cons e' ts)] => if p e' then cons e [AndOrTree.filter p c]
                             else cons e ts
| cons e (nil :: ts)         => AndOrTree.filter p <| cons e ts
| cons e (cons e' ts' :: ts) => if p e' then cons e (cons e' ts' :: AndOrTree.filter p <$> ts)
                                else AndOrTree.filter p <| cons e ts

/-- Map an expression transformation on an `AndOrTree` -/
partial def AndOrTree.map (f : Expr → Expr) : AndOrTree → AndOrTree
| nil       => nil
| cons e ts => cons (f e) (ts.map <| AndOrTree.map f)

/-- Append at leftmost point, TODO delete -/
def AndOrTree.append (t : AndOrTree) (e : Expr) : AndOrTree :=
  match t with
  | nil               => cons e []
  | cons e' []        => cons e' [cons e []]
  | cons e' (t :: ts) => cons e' (t.append e :: ts)

structure State where
  (conditions : AndOrTree)
  (pc : Nat)
  (refs : RefTable)

abbrev M := MetaM

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

def mkExistsFVars (fvs : List Expr) (e : Expr) : M Expr :=
  match fvs with
  | []        => return e
  | fv :: fvs => do mkAppM ``Exists #[← mkLambdaFVars #[fv] <| ← mkExistsFVars fvs e]

def withStatementStep (f : SierraFile) (s : State)
    (k : State → M α) [Inhabited (M α)] : M α := do
  let types := getTypeRefs f
  let libfuncs := getLibfuncRefs f
  let .some st := f.statements.get? s.pc
    | throwError "Program counter out of bounds"
  let .some i' := libfuncs.find? st.libfunc_id
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
    let inputs := st.args
    let outputs := (st.branches.map BranchInfo.results).join  -- TODO
    for i in [:(inputs.length+outputs.length)] do
      fd_typeList := fd_typeList ++ [← mkAppM `List.get! #[fd_types, .lit <| .natVal i]]
    withGetOrMkNewRefs s.refs (inputs ++ outputs).reverse fd_typeList.reverse [] fun refs fvs => do
      let fd_condition ← whnf <| mkAppN fd_condition (fvs.map Expr.fvar).toArray
      -- Only add new condition if it is not trivial
      let conditions' := if ← isDefEq fd_condition (mkConst ``True) then s.conditions
                         else s.conditions.append fd_condition
      let fd : FuncData i' := FuncData_register i'
      let pc' := fd.pcChange s.pc
      let refs' := fd.refsChange refs (inputs ++ outputs)
      k { conditions := conditions', pc := pc', refs := refs' }
  | _ => throwError "Resolved libfunc does not have name"

partial def statementLoop (f : SierraFile) (finputs : List (Nat × Identifier))
    (s : State) (gas : ℕ := 25) : M Expr := do
  let st := f.statements.get! s.pc  -- `sinputs` are the returned cells
  if gas = 0 then return s.conditions.toExpr
  match st.libfunc_id with
  | .name "return" [] =>
    -- Filter out conditions refering to "dangling" FVars (mostly due to `drop()`)
    let conditions := s.conditions.filter (¬ ·.hasAnyFVar (¬ (s.refs.toList.map (·.2)).contains ·))
    logInfo "{refs.toList}"
    -- Take the conjunction of all remaining conditions
    let e := conditions.toExpr
    let (ioRefs, intRefs) := s.refs.toList.reverse.partition (·.1 ∈ finputs.map (·.1) ++ st.args)
    -- Existentially close over intermediate references
    let e ← mkExistsFVars (intRefs.map (.fvar ·.2)) e
    -- Lambda-close over input and output references
    let e ← mkLambdaFVars (ioRefs.map (.fvar ·.2)).toArray e
    return e
  | _ =>
    -- Process next statement
    withStatementStep f s fun s' =>
      statementLoop f finputs s' (gas - 1)

def analyzeFile (s : String) : MetaM Format := do
  match parseGrammar s with
  | .ok f =>
    let ⟨_, pc, inputArgs, _⟩ := f.declarations.get! 0  -- TODO Don't we need the output types?
    let e ← statementLoop f inputArgs { conditions := .nil, pc := pc, refs := ∅ }
    ppExpr e
  | .error str => throwError "Could not parse input file:\n{str}"

def code' :=
"type [0] = felt252;

libfunc [0] = felt252_add;
libfunc [1] = dup<[0]>;

[0]([0], [1]) -> ([3]);
[0]([3], [2]) -> ([4]);
return([4]);

[0]@0([0]: [0], [1]: [0], [2]: [0]) -> ([0]);"

#eval analyzeFile code'

#check Expr.containsFVar
