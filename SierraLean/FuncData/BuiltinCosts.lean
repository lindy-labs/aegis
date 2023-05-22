import SierraLean.FuncDataUtil

namespace Sierra.FuncData

def get_builtin_costs : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [.BuiltinCosts] }]

def builtinCostsLibfuncs : Identifier → Option FuncData
| .name "get_builtin_costs" [] .none => get_builtin_costs
| _ => .none
