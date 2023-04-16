import SierraLean.FuncDataUtil
import SierraLean.FuncData.Felt252
import Mathlib.Data.Bool.Basic

open Qq

namespace Sierra.FuncData

def bool_xor_impl : FuncData where
  inputTypes := [q(Bool), q(Bool)]
  branches := [{ outputTypes := [q(Bool)], condition := fun a b ρ => q($ρ = xor $a $b) }]

def bool_or_impl : FuncData where
  inputTypes := [q(Bool), q(Bool)]
  branches := [{ outputTypes := [q(Bool)], condition := fun a b ρ => q($ρ = $a || $b) }]

def bool_and_impl : FuncData where
  inputTypes := [q(Bool), q(Bool)]
  branches := [{ outputTypes := [q(Bool)], condition := fun a b ρ => q($ρ = $a && $b) }]

def bool_not_impl : FuncData where
  inputTypes := [q(Bool)]
  branches := [{ outputTypes := [q(Bool)], condition := fun a ρ => q($ρ = !$a) }]

def bool_to_felt252 : FuncData where
  inputTypes := [q(Bool)]
  branches := [{ outputTypes := [q(F)], condition := fun a ρ => q($ρ = if $a then 1 else 0) }]

def boolLibfuncs : Identifier → Option FuncData
| .name "bool_xor_impl" []   => bool_xor_impl
| .name "bool_or_impl" []    => bool_or_impl 
| .name "bool_and_impl" []   => bool_and_impl
| .name "bool_not_impl" []   => bool_not_impl
| .name "bool_to_felt252" [] => bool_to_felt252
| _                          => .none
