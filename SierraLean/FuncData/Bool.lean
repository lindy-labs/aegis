import SierraLean.FuncDataUtil
import SierraLean.FuncData.Felt252
import Mathlib.Data.Bool.Basic

open Qq Sierra.SierraType

def Bool.toSierraBool : Bool → Unit ⊕ Unit
| false => .inl ()
| true => .inr ()

namespace Sierra

def SierraType.Bool : SierraType := .Enum [.Struct [], .Struct []]

def SierraBool.toBool : Unit ⊕ Unit → Bool
| .inl () => false
| .inr () => true

instance : Coe (Unit ⊕ Unit) Bool := ⟨SierraBool.toBool⟩

namespace FuncData

def bool_xor_impl : FuncData where
  inputTypes := [.Bool, .Bool]
  branches := [{ outputTypes := [.Bool],
                 condition := fun (a b ρ : Q(Unit ⊕ Unit)) => q($ρ = (xor $a $b).toSierraBool) }]

def bool_or_impl : FuncData where
  inputTypes := [.Bool, .Bool]
  branches := [{ outputTypes := [.Bool],
                 condition := fun (a b ρ : Q(Unit ⊕ Unit)) => q($ρ = ($a || $b).toSierraBool) }]

def bool_and_impl : FuncData where
  inputTypes := [.Bool, .Bool]
  branches := [{ outputTypes := [.Bool],
                 condition := fun (a b ρ : Q(Unit ⊕ Unit)) => q($ρ = ($a && $b).toSierraBool) }]

def bool_not_impl : FuncData where
  inputTypes := [.Bool]
  branches := [{ outputTypes := [.Bool],
                 condition := fun (a ρ : Q(Unit ⊕ Unit)) => q($ρ = (!$a).toSierraBool) }]

def bool_to_felt252 : FuncData where
  inputTypes := [.Bool]
  branches := [{ outputTypes := [Felt252],
                 condition := fun (a : Q(Unit ⊕ Unit)) (ρ : Q(F)) => q($ρ = if $a then 1 else 0) }]

def boolLibfuncs : Identifier → Option FuncData
| .name "bool_xor_impl" []   _ => bool_xor_impl
| .name "bool_or_impl" []    _ => bool_or_impl 
| .name "bool_and_impl" []   _ => bool_and_impl
| .name "bool_not_impl" []   _ => bool_not_impl
| .name "bool_to_felt252" [] _ => bool_to_felt252
| _                            => .none
