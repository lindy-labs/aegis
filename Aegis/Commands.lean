import Aegis.Analyzer

open Lean Meta Elab Command Qq

namespace Sierra

/- Utilities -/

/-- A version of `BranchData` which we are able to persist in `.olean` files -/
structure PersistantBranchData where
  (outputTypes : List SierraType)
  (ioRefs : List FVarId)
  (condition : Q(Prop))

/-- A version of `FuncData` which we are able to persist in `.olean` files -/
structure PersistantFuncData where
  (metadataRef : FVarId)
  (inputTypes : List SierraType)
  (branches : List PersistantBranchData)

def BranchData.persist (inputTypes : List SierraType) (bd : BranchData inputTypes)
    : MetaM PersistantBranchData := do
  let fds ← (inputTypes ++ bd.outputTypes).mapM fun _ => mkFreshFVarId
  pure { outputTypes := bd.outputTypes
         ioRefs := fds
         condition := ← bd.condition.toExpr }

def FuncData.persist (fd : FVarId → FuncData) : MetaM PersistantFuncData := do
  let fv ← mkFreshFVarId
  let bd ← (fd fv).branches.mapM (BranchData.persist (fd fv).inputTypes)
  pure { metadataRef := fv
         inputTypes := (fd fv).inputTypes
         branches := bd }

def PersistantBranchData.unpersist (inputTypes : List SierraType) (subst : FVarSubst)
    (pbd : PersistantBranchData) :
    BranchData inputTypes :=
  let c := FVarSubst.apply subst pbd.condition
  { outputTypes := pbd.outputTypes
    condition := OfInputs.abstract fun args => Expr.beta c args.toArray }

def PersistantFuncData.unpersist (pfd : PersistantFuncData) (fv : FVarId) : FuncData :=
  let s := FVarSubst.empty.insert pfd.metadataRef <| .fvar fv
  { inputTypes := pfd.inputTypes
    branches := pfd.branches.map (PersistantBranchData.unpersist pfd.inputTypes s) }

/-- Copied from Lean.Elab.MutualDef -/
private def declValToTerm (declVal : Syntax) : MacroM Syntax := withRef declVal do
  if declVal.isOfKind ``Parser.Command.declValSimple then
    Term.expandWhereDeclsOpt declVal[2] declVal[1]
  else if declVal.isOfKind ``Parser.Command.declValEqns then
    Term.expandMatchAltsWhereDecls declVal[0]
  -- else if declVal.isOfKind ``Parser.Command.whereStructInst then
  --   expandWhereStructInst declVal
  else if declVal.isMissing then
    Macro.throwErrorAt declVal "declaration body is missing"
  else
    Macro.throwErrorAt declVal "unexpected declaration body"

/- Initialize environment extensions holding cairo path, sierra file, specs, and soudness
proofs. -/

initialize cairoPath : SimplePersistentEnvExtension System.FilePath (Option System.FilePath) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun _ p => p
    addImportedFn := fun ⟨pss⟩ => (pss.map Array.toList).join.getLast?
  }

initialize loadedSierraFile : SimplePersistentEnvExtension SierraFile (Option SierraFile) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun _ sf => sf
    addImportedFn := fun sfss => Id.run do
      let mut sf? : Option SierraFile := default
      for sfs in sfss do
        for sf in sfs do
          if sf.declarations.length > 0 then
            sf? := sf
      sf?
  }

initialize sierraSpecs : SimplePersistentEnvExtension (Identifier × Name × PersistantFuncData)
    (HashMap Identifier (Name × PersistantFuncData)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun specs (i, n) => specs.insert i n
    addImportedFn := fun ⟨pss⟩ => (HashMap.ofList (pss.map Array.toList).join)
  }

initialize sierraSoundness : SimplePersistentEnvExtension (Identifier × Name)
    (HashMap Identifier Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun specs (i, n) => specs.insert i n
    addImportedFn := fun ⟨pss⟩ => (HashMap.ofList (pss.map Array.toList).join)
  }

/- Provide elaboration functions for the commands -/

def sierraLoadString (s : String) : CommandElabM Unit := do
  match ← liftCoreM <| parseGrammar s with
  | .error str => throwError ("Unable to load string:\n" ++ str)
  | .ok sf => modifyEnv (loadedSierraFile.addEntry · sf)

elab "aegis_load_string " s:str : command => sierraLoadString s.getString

elab "aegis_set_path " s:str : command => do
  let fp : System.FilePath := ⟨s.getString⟩
  unless ← fp.pathExists do throwError "Could not find cairo directory"
  modifyEnv (cairoPath.addEntry · fp)

elab "aegis_load_file " s:str : command => do
  let filePath : System.FilePath := ⟨s.getString⟩
  match filePath.extension with
  | .some "sierra" => sierraLoadString <| ← IO.FS.readFile filePath
  | .some "cairo" =>
    let filePath ← IO.FS.realPath filePath
    let args : IO.Process.SpawnArgs :=
      { cmd := "cairo-compile"
        args := #["--replace-ids", filePath.toString] }
    let child ← IO.Process.output args
    dbg_trace "Compilation stderr: {child.stderr}"
    dbg_trace "Compilation stdout: {child.stdout}"
    sierraLoadString child.stdout
  | _ => throwError "Wrong file extension, must be .cairo or .sierra!"


elab "aegis_info" name:str : command => do  -- TODO change from `str` to `ident`
  let env ← getEnv
  let sf := (loadedSierraFile.getState env).get!
  match ← liftCoreM <| parseIdentifier name.getString with
  | .ok i => do
    withFindByIdentifier sf i fun pc inputs outputs =>
    dbg_trace "Starting pc: {pc}"
    dbg_trace "Input types: {inputs.map (·.2)}"
    dbg_trace "Output types: {outputs}"
    return ()
  | .error str => throwError toString str


elab "aegis_spec " name:str val:declVal : command => do  -- TODO change from `str` to `ident`
  let env ← getEnv
  let sf := (loadedSierraFile.getState env).get!
  let typeDefs ← match buildTypeDefs sf.typedefs with
  | .ok x => pure x
  | .error err => throwError err
  let val ← liftMacroM <| declValToTerm val
  match ← liftCoreM <| parseIdentifier name.getString with
  | .ok i =>
    if (sierraSpecs.getState env).contains i then
      throwError "A specification has already been given"
    withRef val do
      liftTermElabM do
        let ty ← getSpecTypeOfName sf i
        let val ← Term.elabTermEnsuringType val ty
        Term.synthesizeSyntheticMVarsNoPostponing
        let val ← instantiateMVars val
        let name : String := "spec_" ++ name.getString  -- TODO handle name clashes
        addAndCompile <| .defnDecl {  name := name
                                      type := ty
                                      levelParams := []
                                      value := val
                                      hints := default
                                      safety := default }
        withFindByIdentifier sf i fun _ inputArgs outputTypes => do
          -- Generate the `FuncData`
          let fd := funcDataFromCondition typeDefs inputArgs outputTypes val
          let fd ← FuncData.persist fd
          -- Add the spec to the cache
          modifyEnv (sierraSpecs.addEntry · (i, name, fd))
  | .error str => throwError toString str

elab "aegis_prove" name:str val:declVal : command => do
  let env ← getEnv
  let sf := (loadedSierraFile.getState env).get!
  let val ← liftMacroM <| declValToTerm val
  match ← liftCoreM <| parseIdentifier name.getString with
  | .ok i =>
    withRef val do
      liftTermElabM do
        let specs := sierraSpecs.getState env
        let specs := HashMap.ofList <| specs.toList.map fun (i, n, pfd) => (i, n, pfd.unpersist)
        let type ← withLocalDeclsD (← getLocalDeclInfosOfName specs sf i) fun fvs => do
          let ioArgs := fvs[:fvs.size - 1]
          let .some (specName, _) := (sierraSpecs.getState env).find? i
            | throwError "Could not find manual specification for {i}"
          mkForallFVars fvs <| ← mkAppM specName ioArgs
        let val ← Term.elabTermEnsuringType val type
        Term.synthesizeSyntheticMVarsNoPostponing
        let val ← instantiateMVars val
        let name : String := "sound_" ++ name.getString
        let name ← mkFreshUserName name
        addDecl <| .defnDecl {  name := name
                                type := type
                                levelParams := []
                                value := val
                                hints := default
                                safety := default }
        modifyEnv (sierraSoundness.addEntry · (i, name))
  | .error str => throwError toString str

elab "aegis_complete" : command => do
  let env ← getEnv
  let sf := (loadedSierraFile.getState env).get!
  let mut missingDecls : Array Identifier := #[]
  for (i, _) in sf.declarations do
    unless (sierraSoundness.getState env).contains i do missingDecls := missingDecls.push i
  unless missingDecls.size = 0 do throwError
    "Soundness proof not provided for the following declarations: {missingDecls}"
  modifyEnv (loadedSierraFile.addEntry · default)  -- remove saved Sierra file after the command
