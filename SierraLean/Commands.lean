import SierraLean.Analyzer

open Lean Meta Elab Command

namespace Sierra

/- Extend the syntax by sierra commands -/

syntax "sierra_load_string " str : command

syntax "sierra_load_file " str : command

syntax "sierra_spec " ident declVal : command

syntax "sierra_sound " ident : command

/- Initialize environment extensions holding a sierra file and specs -/

initialize loadedSierraFile : SimplePersistentEnvExtension SierraFile SierraFile ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun _ sf => sf
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
  | .ok i =>  let type ← liftTermElabM <| getSpecTypeOfName sf i
              let val' ← liftTermElabM <| Term.elabTermEnsuringType (Syntax.getArgs val)[1]! type
              return ()
  | .error str => throwError toString str

#check Syntax