import SierraLean.Analyzer

open Lean Meta Elab Command

namespace Sierra

/- Utilities -/

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

/- Initialize environment extensions holding cairo path, sierra file and specs -/

initialize cairoPath : SimplePersistentEnvExtension System.FilePath (Option System.FilePath) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun _ p => p
    addImportedFn := fun pss => pss.join.back?
  }

initialize loadedSierraFile : SimplePersistentEnvExtension SierraFile SierraFile ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun _ sf => sf
    addImportedFn := fun _ => default -- Load the empty Sierra file by default
  }

initialize sierraSpecs : SimplePersistentEnvExtension (Identifier × Name × FuncData)
    (HashMap Identifier (Name × FuncData)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun specs (i, n) => specs.insert i n
    addImportedFn := (HashMap.ofList ·.join.toList)
  }

/- Provide elaboration functions for the commands -/

def sierraLoadString (s : String) : CommandElabM Unit :=
  match parseGrammar s with
  | .error str => throwError ("Unable to load string:\n" ++ str)
  | .ok sf => modifyEnv (loadedSierraFile.addEntry · sf)

elab "sierra_load_string " s:str : command => sierraLoadString s.getString

elab "sierra_set_path " s:str : command => do
  let fp : System.FilePath := ⟨s.getString⟩
  unless ← fp.pathExists do throwError "Could not find cairo directory"
  modifyEnv (cairoPath.addEntry · fp)

elab "sierra_load_file " s:str : command => do
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

elab "sierra_spec " name:str val:declVal : command => do  -- TODO change from `str` to `ident`
  let env ← getEnv
  let sf := loadedSierraFile.getState env
  let typeDefs ← match buildTypeDefs sf.typedefs with
  | .ok x => pure x
  | .error err => throwError err
  let val ← liftMacroM <| declValToTerm val 
  match Megaparsec.Parsec.parse identifierP name.getString with
  | .ok i =>  
    withRef val do
      liftTermElabM do 
        let type ← getSpecTypeOfName sf i
        let val ← Term.elabTermEnsuringType val type
        Term.synthesizeSyntheticMVarsNoPostponing
        let val ← instantiateMVars val
        let name : String := "spec_" ++ name.getString  -- TODO handle name clashes
        addAndCompile <| .defnDecl {  name := name
                                      type := type
                                      levelParams := []
                                      value := val
                                      hints := default
                                      safety := default }
        withFindByIdentifier sf i fun _ _ inputArgs outputTypes =>
          -- Generate the `FuncData`
          let fd := funcDataFromCondition typeDefs inputArgs outputTypes val
          -- Add the spec to the cache
          modifyEnv fun env => sierraSpecs.addEntry env (i, name, fd)
  | .error str => throwError toString str

elab "sierra_sound" name:str val:declVal : command => do
  let env ← getEnv
  let sf := loadedSierraFile.getState env
  let val ← liftMacroM <| declValToTerm val
  match Megaparsec.Parsec.parse identifierP name.getString with
  | .ok i =>  
    withRef val do
      liftTermElabM do
        let specs := sierraSpecs.getState env
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
  | .error str => throwError toString str
