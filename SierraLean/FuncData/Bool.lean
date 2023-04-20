import SierraLean.FuncDataUtil
import SierraLean.FuncData.Felt252
import Mathlib.Data.Bool.Basic

open Qq Sierra.SierraType

namespace Sierra.FuncData

def bool_xor_impl : FuncData where
  inputTypes := [SierraBool, SierraBool]
  branches := [{
    outputTypes := [SierraBool],
    condition := fun (a : Q(Bool)) (b : Q(Bool)) (ρ : Q(Bool)) => q($ρ = xor $a $b)
  }]

def bool_or_impl : FuncData where
  inputTypes := [SierraBool, SierraBool]
  branches := [{
    outputTypes := [SierraBool],
    condition := fun (a : Q(Bool)) (b : Q(Bool)) (ρ : Q(Bool)) => q($ρ = $a || $b)
  }]

def bool_and_impl : FuncData where
  inputTypes := [SierraBool, SierraBool]
  branches := [{
    outputTypes := [SierraBool],
    condition := fun (a : Q(Bool)) (b : Q(Bool)) (ρ : Q(Bool)) => q($ρ = $a && $b)
  }]

def bool_not_impl : FuncData where
  inputTypes := [SierraBool]
  branches := [{
    outputTypes := [SierraBool],
    condition := fun (a : Q(Bool)) (ρ : Q(Bool)) => q($ρ = !$a)
  }]

def bool_to_felt252 : FuncData where
  inputTypes := [SierraBool]
  branches := [{
    outputTypes := [Felt252],
    condition := fun (a : Q(Bool)) (ρ : Q(F)) => q($ρ = if $a then 1 else 0)
  }]

def boolLibfuncs : Identifier → Option FuncData
| .name "bool_xor_impl" []   => bool_xor_impl
| .name "bool_or_impl" []    => bool_or_impl 
| .name "bool_and_impl" []   => bool_and_impl
| .name "bool_not_impl" []   => bool_not_impl
| .name "bool_to_felt252" [] => bool_to_felt252
| _                          => .none
