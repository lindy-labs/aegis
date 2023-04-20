import SierraLean.FuncDataUtil
import Mathlib.Data.ZMod.Basic

open Qq Sierra.SierraType

namespace Sierra

namespace FuncData

def u128_overflowing_add : FuncData where
  inputTypes := [U128, U128]
  branches := [{
    outputTypes := [U128],
    condition := fun (a : Q(F)) (b : Q(F)) (ρ : Q(F)) => q($ρ = $a + $b)
  }]

def u128_overflowing_sub : FuncData where
  inputTypes := [U128, U128]
  branches := [{
    outputTypes := [U128],
    condition := fun (a : Q(F)) (b : Q(F)) (ρ : Q(F)) => q($ρ = $a - $b)
  }]

def uint128Libfuncs : Identifier → Option FuncData
| .name "u128_overflowing_add" [] => u128_overflowing_add
| .name "u128_overflowing_sub" [] => u128_overflowing_sub
| _                               => .none
