import Aegis.Types

open Qq Sierra
namespace Sierra.FuncData

def withdraw_gas_all : FuncData where
  inputTypes := [.RangeCheck, .GasBuiltin, .BuiltinCosts]
  branches := [{ outputTypes := [.RangeCheck, .GasBuiltin]
                 condition := fun _ (g c : Q(Nat)) _ (g' : Q(Nat)) =>
                   q($c ≤ $g ∧ $g' = $g - $c) },
               { outputTypes := [.RangeCheck, .GasBuiltin]
                 condition := fun _ (g c : Q(Nat)) _ (_ : Q(Nat)) =>
                   q($g < $c) }]  -- TODO maybe we have `$g' = $g`, but that's just guesswork

def gasBuiltinLibfuncs : Identifier → Option FuncData
| .name "withdraw_gas_all" [] .none => withdraw_gas_all
| _ => .none
