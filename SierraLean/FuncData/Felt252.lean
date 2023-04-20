import SierraLean.FuncDataUtil
import Mathlib.Data.ZMod.Basic

open Qq Sierra.SierraType

namespace Sierra
namespace FuncData

def felt252_const (n : Q(Int)) : FuncData where
  inputTypes := []
  branches := [{
    outputTypes := [Felt252],
    condition := fun (a : Q(F)) => q($a = ($n : F))
  }]

def felt252_add : FuncData where
  inputTypes := [Felt252, Felt252]
  branches := [{
    outputTypes := [Felt252],
    condition := fun (a : Q(F)) (b : Q(F)) (ρ : Q(F)) => q($ρ = $a + $b)
  }]

def felt252_sub : FuncData where
  inputTypes := [Felt252, Felt252]
  branches := [{
    outputTypes := [Felt252],
    condition := fun (a : Q(F)) (b : Q(F)) (ρ : Q(F)) => q($ρ = $a - $b)
  }]

def felt252_mul : FuncData where
  inputTypes := [Felt252, Felt252]
  branches := [{
    outputTypes := [Felt252],
    condition := fun (a : Q(F)) (b : Q(F)) (ρ : Q(F)) => q($ρ = $a * $b)
  }]

def felt252_is_zero : FuncData where
  inputTypes := [Felt252]
  branches := [
    { outputTypes := [],
      condition := fun (a : Q(F)) => q($a = 0)
    },
    { outputTypes := [Felt252], -- TODO Actually the condition is baked into the output type here
      condition := fun (a : Q(F)) (_ : Q(F)) => q($a ≠ 0)
    }]

def felt252Libfuncs : Identifier → Option FuncData
| .name "felt252_const" [.const n] => FuncData.felt252_const q($n)
| .name "felt252_add" []           => FuncData.felt252_add
| .name "felt252_sub" []           => FuncData.felt252_sub
| .name "felt252_mul" []           => FuncData.felt252_mul
| .name "felt252_is_zero" []       => FuncData.felt252_is_zero
| _                                => .none
