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
deriving Inhabited, Repr

instance : ToString AndOrTree where toString x := toString $ repr x

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
| cons (.const ``True _) ts => Expr.mkOrs <| (AndOrTree.toExpr <$> ts)
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

partial def AndOrTree.isNil : AndOrTree → Bool
| nil      => true
| cons _ _ => false

/-- Append at leftmost point, TODO delete -/
def AndOrTree.append (t : AndOrTree) (e : Expr) : AndOrTree :=
  match t with
  | nil               => cons e []
  | cons e' []        => cons e' [cons e []]
  | cons e' (t :: ts) => cons e' (t.append e :: ts)

structure State where
  (pc : Nat)
  (refs : RefTable)
  (lctx : LocalContext)
  (types : HashMap Identifier Identifier)
  (libfuncs : HashMap Identifier Identifier)
  deriving Inhabited

abbrev M := StateT State MetaM

def getOrMkNewRef (n : ℕ) (type : Expr) : M FVarId := do
  let s ← get
  match s.refs.find? n with
  | .some x => pure x
  | _ => do
    let name ← mkFreshUserName ("ref" ++ n.repr : String)
    let fv ← mkFreshFVarId
    let lctx' := (← get).lctx.mkLocalDecl fv name type
    set { s with lctx := lctx', refs := s.refs.insert n fv }
    return fv

def getOrMkNewRefs (ns : List ℕ) (types : List Expr) (fvs : List FVarId := []) : M (List FVarId) :=
  match ns, types with
  | (n :: ns), (t :: ts) => do
    let fv ← getOrMkNewRef n t
    getOrMkNewRefs ns ts (fv :: fvs)
  | [],        []        => return fvs
  | _,         _         => panic "types and ref list not the same length!"

def mkExistsFVars (fvs : List Expr) (e : Expr) : M Expr :=
  match fvs with
  | []        => return e
  | fv :: fvs => do mkAppM ``Exists #[← mkLambdaFVars #[fv] <| ← mkExistsFVars fvs e]

def createFuncDataExpr (istr : String) (params : List Parameter)
    (types : HashMap Identifier Identifier) : M Expr := do
  let mut fd := mkConst ("Sierra" ++ "FuncData" ++ istr)
  for p in params do
    match p with
    | .const n => fd := mkApp fd <| .lit <| .natVal n
    | .identifier t => 
        let .some t' := types.find? t
          | throwError "Could not find referenced type"
        fd := mkApp fd <| Type_register t'
    | _ => fd := fd  -- TODO
  return fd

def processReturn (finputs : List (Nat × Identifier)) (st : Statement) (cs : AndOrTree) :
    M Expr := do
  let s ← get
  -- Filter out conditions refering to "dangling" FVars (mostly due to `drop()`)
  let conditions := cs.filter (¬ ·.hasAnyFVar (¬ (s.refs.toList.map (·.2)).contains ·))
  -- Take the conjunction of all remaining conditions
  let e := conditions.toExpr
  let (ioRefs, intRefs) := s.refs.toList.reverse.partition (·.1 ∈ finputs.map (·.1) ++ st.args)
  withLCtx s.lctx #[] do
    -- Existentially close over intermediate references
    let e ← mkExistsFVars (intRefs.map (.fvar ·.2)) e
    -- Lambda-close over input and output references
    let e ← mkLambdaFVars (ioRefs.map (.fvar ·.2)).toArray e
    return e

def extractConditionHead (istr : String) (params : List Parameter) 
    (types : HashMap Identifier Identifier) : M Expr := do
  let fd ← createFuncDataExpr istr params types
  Meta.mkProjection fd `condition

def extractTypeList (istr : String) (params : List Parameter) 
    (types : HashMap Identifier Identifier) (iolength : ℕ) : M (List Expr) := do
  let fd ← createFuncDataExpr istr params types
  let fd_inputTypes ← Meta.mkProjection fd `inputTypes
  let fd_outputTypes ← Meta.mkProjection fd `outputTypes
  let fd_types ← mkAppM `List.append #[fd_inputTypes, fd_outputTypes]
  let mut fd_typeList : List Expr := []
  for i in [:iolength] do
    fd_typeList := fd_typeList ++ [← mkAppM `List.get! #[fd_types, .lit <| .natVal i]]
  return fd_typeList

partial def processState (f : SierraFile) (finputs : List (Nat × Identifier))
    (gas : ℕ := 25) : M (Statement × AndOrTree) := do
  let s ← get
  let st := f.statements.get! s.pc  -- `sinputs` are the returned cells
  if gas = 0 then return (st, .nil)
  match st.libfunc_id with
  | .name "return" [] => return (st, .nil)
  | _ => do
    let types := getTypeRefs f
    let libfuncs := getLibfuncRefs f
    let inputs := st.args
    let outputs := (st.branches.map BranchInfo.results).join  -- TODO
    let .some st := f.statements.get? s.pc
      | throwError "Program counter out of bounds"
    let .some i'@(.name istr params) := libfuncs.find? st.libfunc_id
      | throwError "Could not find named function in declared libfuncs"  -- TODO catch control flow commands before this
    let fd_condition ← extractConditionHead istr params types
    let fd_typeList ← extractTypeList istr params types (inputs.length+outputs.length)
    let fvs ← getOrMkNewRefs (inputs ++ outputs).reverse fd_typeList.reverse
    let fd_condition ← whnf <| mkAppN fd_condition (fvs.map Expr.fvar).toArray
    let fd : FuncData i' := FuncData_register i'
    let mut st' := st
    let mut bes : List AndOrTree := []
    for bi in st.branches do
      let s ← get
      let pc' := bi.target.getD (s.pc + 1)  -- Fallthrough is the default
      let refs' := fd.refsChange s.refs (inputs ++ outputs)
      set { s with pc := pc', refs := refs' }
      let (st'', es) ← processState f finputs (gas - 1)
      st' := st''
      bes := bes ++ [es]
    if (← isDefEq fd_condition (mkConst ``True)) ∧ bes.all AndOrTree.isNil 
      then return (st', .nil)
      else return (st', .cons fd_condition bes)

def analyzeFile (s : String) : MetaM Format := do
  match parseGrammar s with
  | .ok f =>
    let ⟨_, pc, inputArgs, _⟩ := f.declarations.get! 0  -- TODO Don't we need the output types?
    let initialState : State := { pc := pc,
                                  refs := ∅, 
                                  types := getTypeRefs f, 
                                  libfuncs := getLibfuncRefs f,
                                  lctx := .empty }
    let (e, s) ← StateT.run 
      (do
      let (st, cs) ← processState f inputArgs
      processReturn inputArgs st cs) initialState
    ppExpr e
    --return toString s.refs
  | .error str => throwError "Could not parse input file:\n{str}"

def code' :=
"type [0] = felt252;

libfunc [0] = felt252_add;
libfunc [1] = drop<[0]>;
libfunc [2] = branch_align;
libfunc [3] = jump;

[3]() { 2() };
[0]([0], [1]) -> ([3]);
[0]([3], [2]) -> ([4]);
return([4]);

[0]@0([0]: [0], [1]: [0], [2]: [0]) -> ([0]);"

#eval analyzeFile code'
