import SierraLean.FuncDataUtil

open Qq Lean

namespace Sierra.FuncData

variable (specs : HashMap Identifier (Name × FuncData))

def function_call (i : Identifier) : FuncData :=
  (specs.find! i).2

def functionCallLibfuncs : Identifier → Option FuncData
| .name "function_call" [.userfunc i] .none =>
  if specs.contains i then function_call specs i else .none
| _ => .none
