import SierraLean.FuncData.ControlFlow
import SierraLean.FuncData.Felt252

open Lean Qq

namespace Sierra.FuncData

/-- Compile-time type registry -/ -- TODO decentralize this
def Type_register : Identifier → Q(Type)
| .name "felt252" [] => q(F)
| _ => panic "Type not found in register"

/-- Compile-time function data registry -/
def libfuncs (i : Identifier) : Option FuncData :=
  controlFlowLibfuncs i
  <|> felt252Libfuncs i
