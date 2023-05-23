import SierraLean.FuncDataUtil

open Qq
namespace Sierra.FuncData

def get_builtin_costs : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [.BuiltinCosts]
                 condition := fun (ρ : Q(Nat)) => q($ρ > 0) }]

def builtinCostsLibfuncs : Identifier → Option FuncData
| .name "get_builtin_costs" [] .none => get_builtin_costs
| _ => .none
