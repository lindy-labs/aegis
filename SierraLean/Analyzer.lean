import SierraLean.Parser
import SierraLean.FuncData

open Lean Expr Meta Sierra

namespace Sierra

def getTypeRefs (f : SierraFile) : HashMap Identifier Identifier := HashMap.ofList f.typedefs

def getLibfuncRefs (f : SierraFile) : HashMap Identifier Identifier := HashMap.ofList f.libfuncs

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

def mkExistsFVars (fvs : List Expr) (e : Expr) : MetaM Expr :=
  match fvs with
  | []        => return e
  | fv :: fvs => do mkAppM ``Exists #[← mkLambdaFVars #[fv] <| ← mkExistsFVars fvs e]

def processReturn (finputs : List (Nat × Identifier)) (st : Statement) (cs : AndOrTree) :
    M Expr := do
  let s ← get
  -- Filter out conditions refering to "dangling" FVars (mostly due to `drop()`)
  let cs := cs.filter (¬ ·.hasAnyFVar (¬ (s.refs.toList.map (·.2)).contains ·))
  -- Take the conjunction of all remaining conditions
  let e := cs.toExpr
  let refs := s.refs.toList.reverse
  -- Filter out free variables which do not actually appear in the expression
  let refs := refs.filter (e.containsFVar ·.2)
  let (ioRefs, intRefs) := refs.partition (·.1 ∈ finputs.map (·.1) ++ st.args)
  withLCtx s.lctx #[] do
    -- Existentially close over intermediate references
    let e ← mkExistsFVars (intRefs.map (.fvar ·.2)) e
    -- Lambda-close over input and output references
    let e ← mkLambdaFVars (ioRefs.map (.fvar ·.2)).toArray e
    return e

partial def processState (f : SierraFile) (finputs : List (Nat × Identifier))
    (gas : ℕ := 25) : M (Statement × AndOrTree) := do
  let st := f.statements.get! (← get).pc
  if gas = 0 then return (st, .nil)
  match st.libfunc_id with
  | .name "return" [] => return (st, .nil)
  | _ => do
    --let types := getTypeRefs f
    let libfuncs := getLibfuncRefs f
    let .some st := f.statements.get? (← get).pc
      | throwError "Program counter out of bounds"
    let .some i'@(.name istr _) := libfuncs.find? st.libfunc_id
      | throwError "Could not find named function in declared libfuncs"
    let .some fd := FuncData.libfuncs i'
      | throwError "Could not find libfunc used in code"
    unless fd.branches.length = st.branches.length do
      throwError "Incorrect number of branches to {istr}"
    unless fd.inputTypes.length = st.args.length do
      throwError "Incorrect number of arguments to {istr}"
    let mut st' := st
    let mut bes : List AndOrTree := []
    for (branchIdx, bi) in st.branches.enum do
      let bd := fd.branches.get! branchIdx
      unless bd.outputTypes.length = (st.branches.get! branchIdx).results.length do
        throwError "Incorrect number of results to {istr} at branch {branchIdx}"
      let types := fd.inputTypes ++ bd.outputTypes
      let inOutArgs := st.args ++ (st.branches.get! branchIdx).results
      let fvs := .fvar <$> (← getOrMkNewRefs inOutArgs.reverse types.reverse)
      let c := bd.condition.apply fvs
      let s ← get
      let pc' := bi.target.getD <| s.pc + 1  -- Fallthrough is the default
      let refs' := bd.refsChange inOutArgs s.refs
      set { s with pc := pc', refs := refs' }
      let (st'', es) ← processState f finputs (gas - 1)
      st' := st''
      bes := bes ++ [.cons c [es]]
    match bes with
    | []   => return (st', .nil)
    | [es] => return (st', es)
    | _    => return (st', .cons (mkConst ``True) bes)

def analyzeFile (s : String) : MetaM Format := do
  match parseGrammar s with
  | .ok f =>
    let ⟨_, pc, inputArgs, _⟩ := f.declarations.get! 0  -- TODO Don't we need the output types?
    let initialState : State := { pc := pc,
                                  refs := ∅, 
                                  types := getTypeRefs f, 
                                  libfuncs := getLibfuncRefs f,
                                  lctx := .empty }
    let es ← StateT.run 
      (do
      let (st, cs) ← processState f inputArgs
      processReturn inputArgs st cs) initialState
    ppExpr es.1
    --return toString s.refs
  | .error str => throwError "Could not parse input file:\n{str}"
