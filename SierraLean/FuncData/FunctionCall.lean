import SierraLean.FuncDataUtil

open Qq Lean

namespace Sierra.FuncData

variable (specs : HashMap Identifier (Name × (FVarId → FuncData))) (metadataRef : FVarId)

def function_call (i : Identifier) : FuncData :=
  (specs.find! i).2 metadataRef
  
def functionCallLibfuncs : Identifier → Option FuncData
| .name "function_call" [.userfunc i] .none =>
  if specs.contains i then function_call specs metadataRef i else .none
| _ => .none
