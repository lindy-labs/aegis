import SierraLean.FuncDataUtil
import SierraLean.FuncData.Felt252
import Mathlib.Data.Bool.Basic

open Qq Sierra.SierraType

namespace Sierra

def SierraType.Bool : SierraType := .Enum [.Struct [], .Struct []]

instance : Coe (Unit ⊕ Unit) Bool :=
{ coe := fun x => match x with
                  | .inl () => false
                  | .inr () => true }

namespace FuncData

def bool_xor_impl : FuncData where
  inputTypes := [.Bool, .Bool]
  branches := [{
    outputTypes := [.Bool],
    condition := fun (a : Q(Unit ⊕ Unit)) (b : Q(Unit ⊕ Unit)) (ρ : Q(Unit ⊕ Unit)) => q($ρ = xor $a $b)
  }]

def bool_or_impl : FuncData where
  inputTypes := [.Bool, .Bool]
  branches := [{
    outputTypes := [.Bool],
    condition := fun (a : Q(Unit ⊕ Unit)) (b : Q(Unit ⊕ Unit)) (ρ : Q(Unit ⊕ Unit)) => q($ρ = $a || $b)
  }]

def bool_and_impl : FuncData where
  inputTypes := [.Bool, .Bool]
  branches := [{
    outputTypes := [.Bool],
    condition := fun (a : Q(Unit ⊕ Unit)) (b : Q(Unit ⊕ Unit)) (ρ : Q(Unit ⊕ Unit)) => q($ρ = $a && $b)
  }]

def bool_not_impl : FuncData where
  inputTypes := [.Bool]
  branches := [{
    outputTypes := [.Bool],
    condition := fun (a : Q(Unit ⊕ Unit)) (ρ : Q(Unit ⊕ Unit)) => q($ρ = !$a)
  }]

def bool_to_felt252 : FuncData where
  inputTypes := [.Bool]
  branches := [{
    outputTypes := [Felt252],
    condition := fun (a : Q(Unit ⊕ Unit)) (ρ : Q(F)) => q($ρ = if $a then 1 else 0)
  }]

def boolLibfuncs : Identifier → Option FuncData
| .name "bool_xor_impl" []   _ => bool_xor_impl
| .name "bool_or_impl" []    _ => bool_or_impl 
| .name "bool_and_impl" []   _ => bool_and_impl
| .name "bool_not_impl" []   _ => bool_not_impl
| .name "bool_to_felt252" [] _ => bool_to_felt252
| _                          => .none
