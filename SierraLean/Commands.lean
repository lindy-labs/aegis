import SierraLean.Analyzer
import Init.Meta

open Lean Meta Elab Command

namespace Sierra

/- Extend the syntax by sierra commands -/

syntax "sierra_load_string " str : command

syntax "sierra_load_file " str : command

syntax "sierra_spec " ident : command

syntax "sierra_sound " ident : command

/- Provide elaboration functions for the commands -/

initialize loadedSierraFile : SimplePersistentEnvExtension SierraFile SierraFile ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun _ sf => sf
    addImportedFn := fun _ => default  -- TODO ?
  }

elab "sierra_load_string " s:str : command => do
  match parseGrammar s.getString with
  | .error str => throwError ("Unable to load string:\n" ++ str)
  | .ok sf => modifyEnv fun env => loadedSierraFile.addEntry env sf
