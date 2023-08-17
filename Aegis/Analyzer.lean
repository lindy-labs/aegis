import Aegis.Parser
import Aegis.FuncData
import Aegis.FuncDataUtil

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
  | .name "felt252" [] .none => pure .Felt252
  | .name "u8" [] .none => pure .U8
  | .name "u16" [] .none => pure .U16
  | .name "u32" [] .none => pure .U32
  | .name "u64" [] .none => pure .U64
  | .name "u128" [] .none => pure .U128
  | .name "RangeCheck" [] .none => pure .RangeCheck
  | .name "Enum" (.usertype _ :: l) .none => do
    let l ← flip mapM l fun x => match x with
      | .identifier ident => pure ident
      | _ => throw "Expected Enum parameter to refer a to a type"
    pure <| .Enum (l.map acc.find!)
  | .name "Struct" (.usertype _ :: l) .none => do
    let l ← flip mapM l fun x => match x with
      | .identifier ident => pure ident
      | _ => throw "Expected Enum parameter to refer a to a type"
    pure <| .Struct (l.map acc.find!)
  | .name "NonZero" (Parameter.identifier ident :: []) .none => do
    pure <| .NonZero <| acc.find! ident
  | .name "Box" [l] .none =>
    match l with
    | .identifier ident => pure <| .Box <| acc.find! ident
    | _ => throw "Expected Box parameter to refer to a type"
  | .name "Snapshot" [l] .none =>
    match l with
    | .identifier ident => pure <| .Snapshot <| acc.find! ident
    | _ => throw "Expected Snapshot parameter to refer to a type"
  | .name "Array" [t] .none =>
    match t with
    | .identifier ident => pure <| .Array <| acc.find! ident
    | _ => throw "Expected ARray parameter to refer to a type"
  | .name "U128MulGuarantee" [] .none => pure .U128MulGuarantee
  | .name "Pedersen" [] .none => pure .Pedersen
  | .name "BuiltinCosts" [] .none => pure .BuiltinCosts
  | .name "GasBuiltin" [] .none => pure .GasBuiltin
  | .name "Bitwise" [] .none => pure .Bitwise
  | .name "Uninitialized" [t] .none =>
    match t with
    | .identifier ident => pure <| .Array <| acc.find! ident
    | _ => throw "Expected Uninitalized parameter to refer to a type"
  | .name "Nullable" [t] .none =>
    match t with
    | .identifier ident => pure <| .Nullable <| acc.find! ident
    | _ => throw "Expected Nullable parameter to refer to a type"
  | .name "StorageBaseAddress" [] .none => pure .StorageBaseAddress
  | .name "StorageAddress" [] .none => pure .StorageAddress
  | .name "System" [] .none => pure .System
  | .name "ContractAddress" [] .none => pure .ContractAddress
  | _ => throw s!"Unhandled type {ty}"

def buildFuncSignatures
  (currentFunc : Identifier)
  (typedefs : HashMap Identifier SierraType)
  (funcdefs : List (Identifier × Identifier))
  (specs : HashMap Identifier (Name × (FVarId → FuncData)))
  (metadataRef : FVarId) :
  HashMap Identifier FuncData := Id.run do
  let mut acc := ∅
  for (name, sig) in funcdefs do
    match FuncData.libfuncs currentFunc typedefs specs metadataRef sig with
    | some sig => acc := acc.insert name sig
    | none => () --throw <| toString name ++ " : no such libfunc"
  return acc
 
structure State where
  (pc : Nat)
  (refs : RefTable)
  (lctx : LocalContext := .empty)
  (outputRefs : List FVarId)
  (outputTypes : List Identifier)
  (metadataRef : FVarId)
  deriving Inhabited

abbrev M := StateT State MetaM

def getOrMkNewRef (n : ℕ) (t : Expr) : M FVarId := do
  let s ← get
  match s.refs.find? n with
  | .some x => pure x
  | _ => do
    let name ← mkFreshUserName ("ref" ++ n.repr : String)
    let fv ← mkFreshFVarId
    let lctx' := (← get).lctx.mkLocalDecl fv name t
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
    let allRefs := HashSet.ofArray <| s.refs.toArray.map (·.2) ++ s.outputRefs
    let allRefs := allRefs.insert s.metadataRef
    -- Filter out conditions refering to "dangling" FVars (mostly due to `drop()`)
    let cs := cs.filter (¬ ·.hasAnyFVar (¬ allRefs.contains ·))
    -- Partition fvars into input variables and intermediate variables
    let refs := s.refs.toList.reverse
    let (inRefs, intRefs) := (refs.partition (·.1 ∈ finputs.map (·.1)))
    -- Normalize conjunctions and disjunctions in the tree
    let cs := cs.normalize
    -- Disassemble equalities between tuples (disabled for now)
    -- let cs := cs.separateTupleEqs
    -- Contract equalities in the tree
    let cs := cs.contractEqs (Prod.snd <$> intRefs).contains
    -- Compile the three into a single expression
    let e := cs.toExpr
    -- Filter out intermediate variables which do not actually appear in the expression
    let intRefs := intRefs.filter (e.containsFVar ·.2)  
    -- Existentially close over intermediate references
    let e ← mkExistsFVars (intRefs.map (.fvar ·.2)) e
    -- Lambda-close over output references
    let e ← mkLambdaFVars (s.outputRefs.map .fvar).toArray e
    -- Lambda-close over input references
    let e ← mkLambdaFVars (inRefs.map (.fvar ·.2)).toArray e
    -- Lambda-close over metadata reference
    let e ← mkLambdaFVars #[.fvar s.metadataRef] e
    return e

partial def processState
  (typeDefs : HashMap Identifier SierraType)
  (funcSigs : HashMap Identifier FuncData)
  (f : SierraFile)
  (finputs : List (Nat × Identifier))
  (gas : ℕ := 2500) : M (Statement × AndOrTree) := do
  let st := f.statements.get! (← get).pc
  if gas = 0 then return (st, .nil)
  match st.libfunc_id with
  | .name "return" [] .none =>
    let s ← get
    let es := (s.outputRefs.zip (st.args.map fun n => s.refs.find! n)).zip s.outputTypes
    let es := es.map fun ((ofv, rfv), t) =>
      Expr.mkEq (SierraType.toQuote <| typeDefs.find! t) (.fvar rfv) (.fvar ofv)
    return (st, .cons (Expr.mkAnds es) [])
  | _ => do
    let .some st := f.statements.get? (← get).pc
      | throwError "Program counter out of bounds"
    let .some fd := funcSigs.find? st.libfunc_id
      | throwError "Could not find libfunc used in code: {st.libfunc_id}"
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
      -- The new condition to be added
      let c := headBeta <| bd.condition.apply fvs  -- Apply fvars to condition and beta reduce
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
    (k : (pc : ℕ) → List (ℕ × Identifier) → List Identifier → n α) : n α := do
  match (sf.declarations.filter (·.1 == ident)) with
  | [] => throwError "No function with matching identifier found in Sierra file"
  | [⟨_, pc, inputArgs, outputTypes⟩] => k pc inputArgs outputTypes
  | _ => throwError "Ambiguous identifier, please edit Sierra file to make them unique"

def funcDataFromCondition (typeDefs : HashMap Identifier SierraType) 
    (inputArgs : List (ℕ × Identifier))
    (outputTypes : List Identifier)
    (cond : Expr)
    (metadataRef : FVarId) : FuncData :=
  let cond := cond.beta #[.fvar metadataRef]
  { inputTypes := inputArgs.map fun (_, i) => typeDefs.find! i
    branches := [{ outputTypes := outputTypes.map typeDefs.find!
                   condition := OfInputs.abstract fun ios =>
                     mkAppN cond ios.toArray }] }

variable (specs : HashMap Identifier (Name × (FVarId → FuncData)))

partial def getFuncCondition (ident : Identifier) (pc : ℕ) (inputArgs : List (ℕ × Identifier))
    (outputTypes : List Identifier) : MetaM Expr := do
  let typeDefs ← match buildTypeDefs sf.typedefs with
    | .ok x => pure x
    | .error err => throwError err
  let mut lctx : LocalContext := .empty
  let mut outputRefs : Array FVarId := #[]
  for t in outputTypes do
    let name ← mkFreshUserName `ρ
    let fv ← mkFreshFVarId
    lctx := lctx.mkLocalDecl fv name <| SierraType.toQuote <| typeDefs.find! t
    outputRefs := outputRefs.push fv
  -- Create fvar for the reference to the `Metadata` instance
  let metadataRef ← mkFreshFVarId
  lctx := lctx.mkLocalDecl metadataRef (← mkFreshUserName `m) q(Metadata)
  -- Build initial state
  let s : State := { pc := pc
                     refs := ∅
                     lctx := lctx
                     outputRefs := outputRefs.toList
                     outputTypes := outputTypes
                     metadataRef := metadataRef }
  -- Build the function signatures for the declared libfuncs
  let funcSigs := buildFuncSignatures ident typeDefs sf.libfuncs specs metadataRef
  let es ← StateT.run (do
    let mut refs : RefTable := ∅
    -- Add input arguments to initial local context and refs table
    for (i, t) in inputArgs do
      refs := refs.insert i <| ← getOrMkNewRef i <| SierraType.toQuote <| typeDefs.find! t
    set { (← get) with refs := refs }
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
  return OfInputsQ q(Prop) (q(Metadata) :: inputs ++ outputs)

def getSpecTypeOfName (ident : Identifier) : MetaM Q(Type) :=
  withFindByIdentifier sf ident fun _ => getSpecsType sf

def getLocalDeclInfos (ident : Identifier) (pc : ℕ) (inputArgs : List (ℕ × Identifier))
    (outputTypes : List Identifier)
     : MetaM (Array (Name × (Array Expr → n Expr))) := do
  let typeDefs ← match buildTypeDefs sf.typedefs with
    | .ok x => pure x
    | .error err => throwError err
  let mut ret : Array (Name × (Array Expr → n Expr)) := #[]
  ret := ret.push <| .mk (← mkFreshUserName `m) fun _ => pure q(Metadata)
  for (_, t) in inputArgs do
    let n ← mkFreshUserName `a  -- TODO make anonymous?
    ret := ret.push <| .mk n fun _ => pure <| SierraType.toQuote <| typeDefs.find! t
  for t in outputTypes do
    let n ← mkFreshUserName `ρ  -- TODO make anonymous?
    ret := ret.push <| .mk n fun _ => pure <| SierraType.toQuote <| typeDefs.find! t
  let n ← mkFreshUserName `h_auto
  let e ← getFuncCondition sf specs ident pc inputArgs outputTypes
  -- Add the auto spec, to which all previous args are applied
  ret := ret.push <| .mk n fun h_args => pure <| mkAppN e h_args
  return ret

def getLocalDeclInfosOfName (sf : SierraFile) (ident : Identifier) :
    MetaM (Array (Name × (Array Expr → n Expr))) :=
  withFindByIdentifier sf ident <| getLocalDeclInfos sf specs ident

-- TODO delete?
def analyzeFile (s : String) (idx : ℕ := 0) : MetaM Format := do
  match ← parseGrammar s with
  | .ok sf =>
    let ⟨ident, pc, inputArgs, outputTypes⟩ := sf.declarations.get! idx
    let e ← getFuncCondition sf ∅ ident pc inputArgs outputTypes
    let esType ← inferType e
    return (← ppExpr e) ++ "\n Inferred Type:" ++ (← ppExpr esType)
    --return toString es.2.refs
  | .error str => throwError "Could not parse input file:\n{str}"
