import SierraLean.Parser
import SierraLean.FuncData
import SierraLean.FuncDataUtil

open Lean Expr Meta Qq

namespace Sierra

def buildTypeDefs (typedefs : List (Identifier × Identifier)) : Except String (HashMap Identifier SierraType) := do
  let mut acc := HashMap.empty
  for (name, ty) in typedefs do
    let v : SierraType ← go acc ty
    acc := HashMap.insert acc name v
  return acc
where go (acc : _) (ty : Identifier) : Except String SierraType :=
  match ty with
  | .name "felt252" [] => pure SierraType.Felt252
  | .name "u128" [] => pure SierraType.U128
  | .name "Enum" (Parameter.usertype ut :: l) => do
    let l ← flip mapM l fun x => match x with
      | .identifier ident => pure ident
      | _ => throw "Expected Enum parameter to refer a to a type"
    pure <| SierraType.Enum ut (l.map acc.find!)
  | .name "NonZero" (Parameter.identifier ident :: []) => do
    pure <| SierraType.NonZero <| acc.find! ident
  | .name n l => throw <| "Unhandled " ++ n ++ " " ++ (String.intercalate " " <| l.map toString)
  | .ref _ => throw "Unhandled ref"
 
def getLibfuncRefs (f : SierraFile) : HashMap Identifier Identifier := HashMap.ofList f.libfuncs

structure State where
  (pc : Nat)
  (refs : RefTable)
  (lctx : LocalContext)
  (typeDefs : HashMap Identifier SierraType)
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

def mkExistsFVars (fvs : List Expr) (e : Q(Prop)) : MetaM Q(Prop) :=
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
  -- Partition fvars into input or output variables and intermediate variables
  let (ioRefs, intRefs) := refs.partition (·.1 ∈ finputs.map (·.1) ++ st.args)
  -- Filter out intermediate variables which do not actually appear in the expression
  -- let intRefs := intRefs.filter (e.containsFVar ·.2)
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
    let libfuncs := getLibfuncRefs f
    let .some st := f.statements.get? (← get).pc
      | throwError "Program counter out of bounds"
    let .some i'@(.name istr _) := libfuncs.find? st.libfunc_id
      | throwError "Could not find named function in declared libfuncs"
    let .some fd := FuncData.libfuncs (← get).typeDefs i'
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
    let typedefs ← match buildTypeDefs f.typedefs with
      | .ok x => pure x
      | .error err => throwError err
    let initialState : State := { pc := pc,
                                  refs := ∅, 
                                  typeDefs := typedefs, 
                                  libfuncs := getLibfuncRefs f,
                                  lctx := .empty }
    let es ← StateT.run 
      (do
      let (st, cs) ← processState f inputArgs
      processReturn inputArgs st cs) initialState
    let esType ← inferType es.1
    return (← ppExpr es.1) ++ "\n Type:" ++ (← ppExpr esType)
    --return toString es.2.refs
  | .error str => throwError "Could not parse input file:\n{str}"
