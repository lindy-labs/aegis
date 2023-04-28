import SierraLean.Parser
import SierraLean.FuncData
import SierraLean.FuncDataUtil

open Lean Expr Meta Qq

namespace Sierra

def buildTypeDefs (typedefs : List (Identifier × Identifier)) :
    Except String (HashMap Identifier SierraType) := do
  let mut acc := HashMap.empty
  for (name, ty) in typedefs do
    let v : SierraType ← go acc ty
    acc := acc.insert name v
  return acc
where go (acc : _) (ty : Identifier) : Except String SierraType :=
  match ty with
  | .name "felt252" [] => pure .Felt252
  | .name "u32" [] => pure .U32
  | .name "u64" [] => pure .U64
  | .name "u128" [] => pure .U128
  | .name "u256" [] => pure .U256
  | .name "RangeCheck" [] => pure .RangeCheck
  | .name "Enum" (.usertype _ :: l) => do
    let l ← flip mapM l fun x => match x with
      | .identifier ident => pure ident
      | _ => throw "Expected Enum parameter to refer a to a type"
    pure <| .Enum (l.map acc.find!)
  | .name "Struct" (.usertype _ :: l) => do
    let l ← flip mapM l fun x => match x with
      | .identifier ident => pure ident
      | _ => throw "Expected Enum parameter to refer a to a type"
    pure <| .Struct (l.map acc.find!)
  | .name "NonZero" (Parameter.identifier ident :: []) => do
    pure <| .NonZero <| acc.find! ident
  | .name "Box" [l] =>
    match l with
    | .identifier ident => pure <| .Box <| acc.find! ident
    | _ => throw "Expected Box parameter to refer to a type"
  | .name "Snapshot" [l] =>
    match l with
    | .identifier ident => pure <| .Snapshot <| acc.find! ident
    | _ => throw "Expected Snapshot parameter to refer to a type"
  | .name "Array" [t] =>
    match t with
    | .identifier ident => pure <| .Array <| acc.find! ident
    | _ => throw "Expected ARray parameter to refer to a type"
  | .name n l => throw <| "Unhandled " ++ n ++ " " ++ (" ".intercalate <| l.map toString)
  | .ref _ => throw "Unhandled ref"

def buildFuncSignatures
  (typedefs : HashMap Identifier SierraType)
  (funcdefs : List (Identifier × Identifier))
  (specs : HashMap Identifier Name) : HashMap Identifier FuncData := Id.run do
  let mut acc := ∅
  for (name, sig) in funcdefs do
    match FuncData.libfuncs typedefs ∅ specs sig with  -- TODO replace `∅` by previous userfuncs
    | some sig => acc := acc.insert name sig
    | none => () --throw <| toString name ++ " : no such libfunc"
  return acc
 
structure State where
  (pc : Nat)
  (refs : RefTable)
  (lctx : LocalContext := .empty)
  (outputRefs : List FVarId)
  (outputTypes : List Identifier)
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

def processAndOrTree (finputs : List (Nat × Identifier)) (cs : AndOrTree) :
    M Expr := do
  let s ← get
  withLCtx s.lctx #[] do
    let allRefs := s.refs.toList.map (·.2) ++ s.outputRefs
    -- Filter out conditions refering to "dangling" FVars (mostly due to `drop()`)
    let mut cs := cs.filter (¬ ·.hasAnyFVar (¬ allRefs.contains ·))
    -- Take the conjunction of all remaining conditions
    let e := cs.toExpr
    let refs := s.refs.toList.reverse
    -- Partition fvars into input variables and intermediate variables
    let (inRefs, intRefs) := refs.partition (·.1 ∈ finputs.map (·.1))
    -- Filter out intermediate variables which do not actually appear in the expression
    --let intRefs := intRefs.filter (e.containsFVar ·.2)  
    -- Existentially close over intermediate references
    let e ← mkExistsFVars (intRefs.map (.fvar ·.2)) e
    -- Lambda-close over output references
    let e ← mkLambdaFVars (s.outputRefs.map .fvar).toArray e
    -- Lambda-close over input references
    let e ← mkLambdaFVars (inRefs.map (.fvar ·.2)).toArray e
    return e

partial def processState
  (typeDefs : HashMap Identifier SierraType)
  (funcSigs : HashMap Identifier FuncData)
  (f : SierraFile)
  (finputs : List (Nat × Identifier))
  (gas : ℕ := 25) : M (Statement × AndOrTree) := do
  let st := f.statements.get! (← get).pc
  if gas = 0 then return (st, .nil)
  match st.libfunc_id with
  | .name "return" [] =>
    let s ← get
    let es := (s.outputRefs.zip (st.args.map fun n => s.refs.find! n)).zip s.outputTypes
    let es := es.map fun ((ofv, rfv), type) =>
      Expr.mkEq (SierraType.toQuote <| typeDefs.find! type) (.fvar rfv) (.fvar ofv)
    return (st, .cons (Expr.mkAnds es) [])
  | _ => do
    let .some st := f.statements.get? (← get).pc
      | throwError "Program counter out of bounds"
    let .some fd := funcSigs.find? st.libfunc_id
      | throwError "Could not find libfunc used in code"
    unless fd.branches.length = st.branches.length do
      throwError "Incorrect number of branches to {st.libfunc_id}"
    unless fd.inputTypes.length = st.args.length do
      throwError "Incorrect number of arguments to {st.libfunc_id}"
    let mut st' := st
    let mut bes : List AndOrTree := []
    for (branchIdx, bi) in st.branches.enum do
      let bd := fd.branches.get! branchIdx
      unless bd.outputTypes.length = (st.branches.get! branchIdx).results.length do
        throwError "Incorrect number of results to {st.libfunc_id} at branch {branchIdx}"
      let types := fd.inputTypes ++ bd.outputTypes
      let inOutArgs := st.args ++ (st.branches.get! branchIdx).results
      let fvs := .fvar <$> (← getOrMkNewRefs inOutArgs.reverse (types.map SierraType.toQuote).reverse)
      let c := bd.condition.apply fvs
      let s ← get
      let pc' := bi.target.getD <| s.pc + 1  -- Fallthrough is the default
      let refs' := bd.refsChange inOutArgs s.refs
      set { s with pc := pc', refs := refs' }
      let (st'', es) ← processState typeDefs funcSigs f finputs (gas - 1)
      st' := st''
      bes := bes ++ [.cons c [es]]
    match bes with
    | []   => return (st', .nil)
    | [es] => return (st', es)
    | _    => return (st', .cons (mkConst ``True) bes)

variable (sf : SierraFile) {n: Type → Type _} [MonadControlT MetaM n] [Monad n] [MonadError n]

/-- Perform an action after finding a declaration in the file by its identifier. -/
def withFindByIdentifier (ident : Identifier)
    (k : ℕ → List (ℕ × Identifier) → List Identifier → n α) : n α := do
  match sf.declarations.filter (·.1 == ident) with
  | [] => throwError "No function with matching identifier found in Sierra file"
  | [⟨_, pc, inputArgs, outputTypes⟩] => k pc inputArgs outputTypes
  | _ => throwError "Ambiguous identifier, please edit Sierra file to make them unique"

def getFuncCondition (pc : ℕ) (inputArgs : List (ℕ × Identifier)) (outputTypes : List Identifier) 
    (specs : HashMap Identifier Name) : MetaM Expr := do
  let typeDefs ← match buildTypeDefs sf.typedefs with
    | .ok x => pure x
    | .error err => throwError err
  let funcSigs := buildFuncSignatures typeDefs sf.libfuncs specs
  let mut lctx : LocalContext := .empty
  let mut outputRefs : Array FVarId := #[]
  for t in outputTypes do
    let name ← mkFreshUserName `ρ
    let fv ← mkFreshFVarId
    let type := SierraType.toQuote <| typeDefs.find! t
    lctx := lctx.mkLocalDecl fv name type
    outputRefs := outputRefs.push fv
  let s : State := { pc := pc
                     refs := ∅
                     lctx := lctx
                     outputRefs := outputRefs.toList
                     outputTypes := outputTypes }
  let es ← StateT.run (do
    let mut refs : RefTable := ∅
    for (i, t) in inputArgs do
      refs := refs.insert i <| ← getOrMkNewRef i <| SierraType.toQuote <| typeDefs.find! t
    set { s with refs := refs }
    let (_, cs) ← processState typeDefs funcSigs sf inputArgs
    processAndOrTree inputArgs cs) s
  return es.1

/-- Derive specification type independently of the acutal spec, in order to be able to 
type check the spec. -/
def getSpecsType (inputArgs : List (ℕ × Identifier)) (outputTypes : List Identifier) :
    MetaM Q(Type) := do
  let typeDefs ← match buildTypeDefs sf.typedefs with
    | .ok x => pure x
    | .error err => throwError err
  let inputs := inputArgs.map (SierraType.toQuote ∘ (typeDefs.find! ·.2))
  let outputs := outputTypes.map (SierraType.toQuote ∘ typeDefs.find!)
  return OfInputsQ q(Prop) (inputs ++ outputs)

def getSpecTypeOfName (ident : Identifier) : MetaM Q(Type) :=
  withFindByIdentifier sf ident fun _ => getSpecsType sf

variable (specs : HashMap Identifier Name)

def getLocalDeclInfos (pc : ℕ) (inputArgs : List (ℕ × Identifier))
    (outputTypes : List Identifier)
     : MetaM (Array (Name × (Array Expr → n Expr))) := do
  let typeDefs ← match buildTypeDefs sf.typedefs with
    | .ok x => pure x
    | .error err => throwError err
  let mut ret : Array (Name × (Array Expr → n Expr)) := #[]
  for (_, t) in inputArgs do
    let n ← mkFreshUserName `a  -- TODO make anonymous?
    ret := ret.push <| .mk n fun _ => pure <| SierraType.toQuote <| typeDefs.find! t
  for t in outputTypes do
    let n ← mkFreshUserName `ρ  -- TODO make anonymous?
    ret := ret.push <| .mk n fun _ => pure <| SierraType.toQuote <| typeDefs.find! t
  let n ← mkFreshUserName `h_auto
  let e ← getFuncCondition sf pc inputArgs outputTypes specs
  ret := ret.push <| .mk n fun h_args => pure <| mkAppN e h_args
  return ret

def getLocalDeclInfosOfName (sf : SierraFile) (ident : Identifier) :
    MetaM (Array (Name × (Array Expr → n Expr))) :=
  withFindByIdentifier sf ident <| getLocalDeclInfos sf specs

-- TODO delete?
def analyzeFile (s : String) (idx : ℕ := 0) : MetaM Format := do
  match parseGrammar s with
  | .ok sf =>
    let ⟨_, pc, inputArgs, outputTypes⟩ := sf.declarations.get! idx
    let e ← getFuncCondition sf pc inputArgs outputTypes ∅
    let esType ← inferType e
    return (← ppExpr e) ++ "\n Inferred Type:" ++ (← ppExpr esType)
    --return toString es.2.refs
  | .error str => throwError "Could not parse input file:\n{str}"
