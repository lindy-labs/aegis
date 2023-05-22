import SierraLean.FuncDataUtil

namespace Sierra.FuncData

def withdraw_gas_all : FuncData where
  inputTypes := [.RangeCheck, .GasBuiltin, .BuiltinCosts]
  branches := [{ outputTypes := [.RangeCheck, .GasBuiltin] },
               { outputTypes := [.RangeCheck, .GasBuiltin] }]

def gasBuiltinLibfuncs : Identifier → Option FuncData
| .name "withdraw_gas_all" [] .none => withdraw_gas_all
| _ => .none
