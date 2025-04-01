import Aegis.Parser
import Aegis.Libfuncs
import Aegis.Types
import Aegis.Options

open Lean Expr Meta Qq

namespace Sierra

def buildFuncSignatures
  (currentFunc : Identifier)
  (typedefs : Std.HashMap Identifier SierraType)
  (funcdefs : List (Identifier × Identifier))
  (specs : Std.HashMap Identifier (Name × (FVarId → FuncData)))
  (metadataRef : FVarId) :
  MetaM (Std.HashMap Identifier FuncData) := do
  let mut acc := ∅
  for (name, sig) in funcdefs do
    match FuncData.libfuncs currentFunc typedefs specs metadataRef sig with
    | some sig => acc := acc.insert name sig
    | none =>
      if ← Option.isEnabled Options.aegis.trace then
        dbg_trace s!"{toString name}: no libfunc {sig}"
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
  match s.refs[n]? with
  | .some x => pure x
  | _ => do
    let name ← mkFreshUserName (.mkSimple ("ref" ++ n.repr))
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
    let allRefs := Std.HashSet.ofArray <| s.refs.toArray.map (·.2) ++ s.outputRefs
    let allRefs := allRefs.insert s.metadataRef
    -- Filter out conditions refering to "dangling" FVars (mostly due to `drop()`)
    let mut cs := cs.filter (¬ ·.hasAnyFVar (¬ allRefs.contains ·))
    -- Partition fvars into input variables and intermediate variables
    let refs := s.refs.toList
    --logInfo s!"refs: {refs.map (·.1)} \n"
    let (inRefs, intRefs) := (refs.partition (·.1 ∈ finputs.map (·.1)))
    let mut intRefs := intRefs
    -- Normalize conjunctions and disjunctions in the tree
    if ← Sierra.Options.aegis.normalize.isEnabled then cs := cs.normalize
    -- Disassemble equalities between tuples (disabled by default)
    if ← Sierra.Options.aegis.separateTuples.isEnabled then cs := cs.separateTupleEqs
    -- Contract equalities in the tree
    if ← Sierra.Options.aegis.contract.isEnabled then
      cs := cs.contractEqs (Prod.snd <$> intRefs).contains
    -- Compile the three into a single expression
    let e := cs.toExpr
    -- Filter out intermediate variables which do not actually appear in the expression
    if ← Sierra.Options.aegis.filterUnused.isEnabled then
      intRefs := intRefs.filter (e.containsFVar ·.2)
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
  (typeDefs : Std.HashMap Identifier SierraType)
  (funcSigs : Std.HashMap Identifier FuncData)
  (f : SierraFile)
  (finputs : List (Nat × Identifier))
  (gas : ℕ := 2500) : M AndOrTree := do
  let st := f.statements[(← get).pc]!
  if gas = 0 then return .nil
  match st.libfunc_id with
  | .name "return" [] .none =>
    let s ← get
    let es := (s.outputRefs.zip (← st.args.mapM fun n => do
      let .some sn := s.refs[n]?
        | throwError "Could not find reference {n} in ref table"
      pure sn)).zip s.outputTypes
    let es ← es.mapM fun ((ofv, rfv), t) => do
      let .some st := typeDefs[t]?
        | throwError "Could not find type def for {t}"
      pure <| Expr.mkEq (SierraType.toQuote [] <| st) (.fvar rfv) (.fvar ofv)
    return .cons (Expr.mkAnds es) []
  | _ => do
    let .some st := f.statements[(← get).pc]?
      | throwError "Program counter out of bounds"
    let .some fd := funcSigs[st.libfunc_id]?
      | throwError "Could not find libfunc used in code: {st.libfunc_id}"
    unless fd.branches.length = st.branches.length do
      throwError "Incorrect number of branches to {st.libfunc_id}"
    unless fd.inputTypes.length = st.args.length do
      throwError "Incorrect number of arguments to {st.libfunc_id}"
    let mut bes : List AndOrTree := []
    for (bi, branchIdx) in st.branches.zipIdx do
      let bd := fd.branches[branchIdx]!
      unless bd.outputTypes.length = st.branches[branchIdx]!.results.length do
        throwError "Incorrect number of results to {st.libfunc_id} at branch {branchIdx}"
      let types := fd.inputTypes ++ bd.outputTypes
      let inOutArgs := st.args ++ st.branches[branchIdx]!.results
      let fvs := .fvar <$> (← getOrMkNewRefs inOutArgs.reverse (types.map SierraType.toQuote).reverse)
      -- The new condition to be added
      let c := headBeta <| bd.condition.apply fvs  -- Apply fvars to condition and beta reduce
      let pc' := bi.target.getD <| (← get).pc + 1  -- Fallthrough is the default
      set { ← get with pc := pc' }
      let es ← processState typeDefs funcSigs f finputs (gas - 1)
      bes := bes ++ [.cons c [es]]
    match bes with
    | []   => return .nil
    | [es] => return es
    | _    => return .cons (mkConst ``True) bes

variable (sf : SierraFile) {n: Type → Type _} [MonadControlT MetaM n] [Monad n] [MonadError n]

/-- Perform an action after finding a declaration in the file by its identifier. -/
def withFindByIdentifier (ident : Identifier)
    (k : (pc : ℕ) → List (ℕ × Identifier) → List Identifier → n α) : n α := do
  match (sf.declarations.filter (·.1 == ident)) with
  | [] => throwError "No function with matching identifier found in Sierra file"
  | [⟨_, pc, inputArgs, outputTypes⟩] => k pc inputArgs outputTypes
  | _ => throwError "Ambiguous identifier, please edit Sierra file to make them unique"

def funcDataFromCondition (typeDefs : Std.HashMap Identifier SierraType)
    (inputArgs : List (ℕ × Identifier))
    (outputTypes : List Identifier)
    (cond : Expr)
    (metadataRef : FVarId) : FuncData :=
  let cond := cond.beta #[.fvar metadataRef]
  { inputTypes := inputArgs.map fun (_, i) => typeDefs[i]!
    branches := [{ outputTypes := outputTypes.map typeDefs.get!
                   condition := OfInputs.abstract fun ios =>
                     mkAppN cond ios.toArray }] }

variable (specs : Std.HashMap Identifier (Name × (FVarId → FuncData)))
  (contractCalls : List ContractCallData)

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
    let .some st := typeDefs[t]?
      | throwError "Could not find type def for {t}"
    lctx := lctx.mkLocalDecl fv name <| SierraType.toQuote [] st
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
  let funcSigs ← buildFuncSignatures ident typeDefs sf.libfuncs specs metadataRef
  let es ← StateT.run (do
    let mut refs : RefTable := ∅
    -- Add input arguments to initial local context and refs table
    for (i, t) in inputArgs do
      let .some st := typeDefs[t]?
        | throwError "Could not find type def for {t}"
      refs := refs.insert i <| ← getOrMkNewRef i <| SierraType.toQuote [] st
    set { (← get) with refs := refs }
    let cs ← processState typeDefs funcSigs sf inputArgs
    processAndOrTree inputArgs cs) s
  return es.1

/-- Derive specification type independently of the acutal spec, in order to be able to
type check the spec. -/
def getSpecsType (inputArgs : List (ℕ × Identifier)) (outputTypes : List Identifier) :
    MetaM Q(Type) := do
  let typeDefs ← match buildTypeDefs sf.typedefs with
    | .ok x => pure x
    | .error err => throwError err
  let inputs := inputArgs.map (SierraType.toQuote ∘ (typeDefs.get! ·.2))
  let outputs := outputTypes.map (SierraType.toQuote ∘ typeDefs.get!)
  return OfInputsQ q(Prop) (q(Metadata) :: inputs ++ outputs)

def getSpecTypeOfName (ident : Identifier) : MetaM Q(Type) :=
  withFindByIdentifier sf ident fun _ => getSpecsType sf

def buildContractCallHyp (metadataRef : FVarId) (cd : ContractCallData) : MetaM Expr := do
  let ⟨ident, addr, sel, impls⟩ := cd
  unless specs.contains ident do throwError "specification for referenced contract call {ident} not given"
  let cond := (specs[ident]!.2 metadataRef).branches[0]!.condition
  let cond ← cond.toExpr -- TODO change
  let m : Q(Metadata) := Expr.fvar metadataRef
  let cond ← Core.betaReduce cond
  let impls := impls.toArray.map fun ⟨type, _, _⟩ => (`impl, fun _ => pure type.toQuote)
  withLocalDeclsD impls fun inputImpls =>
    let cond := mkAppN cond inputImpls
    withLocalDeclD `s q(System) fun s =>
      let cond := mkApp cond s
      withLocalDeclD `d q(List F) fun d =>
        let cond := mkApp cond d
        withLocalDeclsD impls fun outputImpls =>
          let cond := mkAppN cond outputImpls
          withLocalDeclD `s' q(System) fun s' => do
            let cond := mkApp cond s'
            let cr := q($(m).callResult $addr $sel)
            let caller := q($(m).contractAddress)
            let cr := mkAppN cr #[d, caller, s]
            -- Wrap the first `callResult` component into the quotation of a `PanicResult` to match
            -- the return type of wrappers
            let sumInl : Q(List F → List F ⊕ Unit × List F) := q(Sum.inl)
            let cond := mkApp cond <| mkApp sumInl <| .proj `Prod 0 cr
            -- Add Statement about post-call system state
            let systemCond := Sierra.Expr.mkEq q(System) s' <| .proj `Prod 1 cr
            let cond ← mkArrow systemCond cond
            mkForallFVars (inputImpls ++ [s, d] ++ outputImpls ++ [s']) cond

def getLocalDeclInfos (ident : Identifier) (pc : ℕ) (inputArgs : List (ℕ × Identifier))
    (outputTypes : List Identifier)
     : MetaM (Array (Name × (Array Expr → Elab.Term.TermElabM Expr))) := do
  let typeDefs ← match buildTypeDefs sf.typedefs with
    | .ok x => pure x
    | .error err => throwError err
  let mut ret : Array (Name × (Array Expr → Elab.Term.TermElabM Expr)) := #[]
  ret := ret.push <| .mk (← mkFreshUserName `m) fun _ => pure q(Metadata)
  for (_, t) in inputArgs do
    let n ← mkFreshUserName `a  -- TODO make anonymous?
    ret := ret.push <| .mk n fun _ => pure <| SierraType.toQuote [] <| typeDefs[t]!
  for t in outputTypes do
    let n ← mkFreshUserName `ρ  -- TODO make anonymous?
    ret := ret.push <| .mk n fun _ => pure <| SierraType.toQuote [] <| typeDefs[t]!
  -- Add the callResult specs, to which the metadata reference is applied
  for cd in contractCalls do
    ret := ret.push <| .mk `callSpec fun call_args => do
      let metadataRef := call_args[0]! |> fvarId!
      buildContractCallHyp specs metadataRef cd
  let n ← mkFreshUserName `h_auto
  let e ← getFuncCondition sf specs ident pc inputArgs outputTypes
  -- Add the auto spec, to which all previous args are applied
  ret := ret.push <| .mk n fun h_args =>
    pure <| mkAppN e <| h_args.extract 0 (h_args.size - contractCalls.length)
  return ret

def getLocalDeclInfosOfName (sf : SierraFile) (ident : Identifier) :
    MetaM (Array (Name × (Array Expr → Elab.Term.TermElabM Expr))) :=
  withFindByIdentifier sf ident <| getLocalDeclInfos sf specs contractCalls ident

-- TODO delete?
def analyzeFile (s : String) (idx : ℕ := 0) : MetaM Format := do
  match ← parseGrammar s with
  | .ok sf =>
    let ⟨ident, pc, inputArgs, outputTypes⟩ := sf.declarations[idx]!
    let e ← getFuncCondition sf ∅ ident pc inputArgs outputTypes
    let esType ← inferType e
    return (← ppExpr e) ++ "\n Inferred Type:" ++ (← ppExpr esType)
    --return toString es.2.refs
  | .error str => throwError "Could not parse input file:\n{str}"
