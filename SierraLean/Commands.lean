import SierraLean.Analyzer

open Lean Meta Elab Command

namespace Sierra

/- Initialize environment extensions holding a sierra file and specs -/

initialize loadedSierraFile : SimplePersistentEnvExtension SierraFile SierraFile ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun _ sf => sf
    addImportedFn := fun _ => default  -- TODO ?
  }

initialize sierraSpecs : SimplePersistentEnvExtension (Identifier × Name)
    (HashMap Identifier Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun specs (i, n) => specs.insert i n
    addImportedFn := fun _ => default  -- TODO ?
  }

/- Provide elaboration functions for the commands -/

def sierraLoadString (s : String) : CommandElabM Unit :=
  match parseGrammar s with
  | .error str => throwError ("Unable to load string:\n" ++ str)
  | .ok sf => modifyEnv fun env => loadedSierraFile.addEntry env sf

elab "sierra_load_string " s:str : command => sierraLoadString s.getString

elab "sierra_load_file " s:str : command => do
  sierraLoadString <| ← IO.FS.readFile <| .mk s.getString

elab "sierra_spec " name:str val:declVal : command => do  -- TODO change from `str` to `ident`
  let env ← getEnv
  let sf := loadedSierraFile.getState env
  match Megaparsec.Parsec.parse identifierP name.getString with
  | .ok i =>  liftTermElabM do 
                let type ← getSpecTypeOfName sf i
                let val ← Term.elabTermEnsuringType (Syntax.getArgs val)[1]! type
                Term.synthesizeSyntheticMVarsNoPostponing
                let val ← instantiateMVars val
                let name : String := "spec_" ++ name.getString  -- TODO handle name clashes
                addAndCompile <| .defnDecl {  name := name
                                              type := type
                                              levelParams := []
                                              value := val
                                              hints := default
                                              safety := default }
                -- Add the spec to the cache
                modifyEnv fun env => sierraSpecs.addEntry env (i, name)
  | .error str => throwError toString str

elab "sierra_sound" name:str val:declVal : command => do
  let env ← getEnv
  let sf := loadedSierraFile.getState env
  match Megaparsec.Parsec.parse identifierP name.getString with
  | .ok i =>  
    liftTermElabM do
      let type ← withLocalDeclsD (← getLocalDeclInfosOfName sf i) fun fvs => do
        let ioArgs := fvs[:fvs.size - 1]
        let .some specName := (sierraSpecs.getState env).find? i
          | throwError "Could not find manual specification for {i}"
        mkForallFVars fvs <| ← mkAppM specName ioArgs
      let val ← Term.elabTermEnsuringType (Syntax.getArgs val)[1]! type
      Term.synthesizeSyntheticMVarsNoPostponing
      let val ← instantiateMVars val
      let name : String := "sound_" ++ name.getString
      addDecl <| .defnDecl {  name := name
                              type := type
                              levelParams := []
                              value := val
                              hints := default
                              safety := default }
  | .error str => throwError toString str
