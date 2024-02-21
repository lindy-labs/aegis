import Aegis.Types

open Qq Sierra Lean
namespace Sierra.FuncData

variable (currentFunc : Identifier) (metadataRef : FVarId)

def withdraw_gas_all : FuncData where
  inputTypes := [.RangeCheck, .GasBuiltin, .BuiltinCosts]
  branches := [{ outputTypes := [.RangeCheck, .GasBuiltin]
                 condition := fun _ (g c : Q(Nat)) _ (g' : Q(Nat)) =>
                   q($c ≤ $g ∧ $g' = $g - $c) },
               { outputTypes := [.RangeCheck, .GasBuiltin]
                 condition := fun _ (g c : Q(Nat)) _ (_ : Q(Nat)) =>
                   q($g < $c) }]  -- TODO maybe we have `$g' = $g`, but that's just guesswork

#check Metadata.costs

def withdraw_gas : FuncData where
  inputTypes := [.RangeCheck, .GasBuiltin]
  branches := [{ outputTypes := [.RangeCheck, .GasBuiltin]
                 condition := fun _ (g : Q(Nat)) _ (g' : Q(Nat)) =>
                   let m : Q(Metadata) := .fvar metadataRef
                   q(($m).costs $currentFunc ≤ $g ∧ $g' = $g - ($m).costs $currentFunc) },
               { outputTypes := [.RangeCheck, .GasBuiltin]
                 condition := fun _ (g : Q(Nat)) _ _ =>
                   let m : Q(Metadata) := .fvar metadataRef
                   q($g < ($m).costs $currentFunc) }]

def gasBuiltinLibfuncs : Identifier → Option FuncData
| .name "withdraw_gas_all" [] .none => withdraw_gas_all
| .name "withdraw_gas" [] .none => withdraw_gas currentFunc metadataRef
| _ => .none
