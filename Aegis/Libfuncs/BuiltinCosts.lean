import Aegis.Types

open Qq Lean
namespace Sierra.FuncData

variable (currentFunc : Identifier) (metadataRef : FVarId)

def get_builtin_costs : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [.BuiltinCosts]
                 condition := fun (ρ : Q(Nat)) =>
                   let m : Q(Metadata) := .fvar metadataRef
                   q($ρ = ($m).costs $currentFunc) }]

def builtinCostsLibfuncs : Identifier → Option FuncData
| .name "get_builtin_costs" [] .none => get_builtin_costs currentFunc metadataRef
| _ => .none
