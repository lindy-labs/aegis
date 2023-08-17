import Aegis.Types
import Mathlib.Data.ZMod.Basic

open Qq Sierra.SierraType

namespace Sierra.FuncData

def felt252_const (n : Q(F)) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [Felt252]
                 condition := fun (a : Q(F)) => q($a = $n) }]

def felt252_add : FuncData where
  inputTypes := [Felt252, Felt252]
  branches := [{ outputTypes := [Felt252]
                 condition := fun (a : Q(F)) (b : Q(F)) (ρ : Q(F)) => q($ρ = $a + $b) }]

def felt252_sub : FuncData where
  inputTypes := [Felt252, Felt252]
  branches := [{ outputTypes := [Felt252]
                 condition := fun (a : Q(F)) (b : Q(F)) (ρ : Q(F)) => q($ρ = $a - $b) }]

def felt252_mul : FuncData where
  inputTypes := [Felt252, Felt252]
  branches := [{ outputTypes := [Felt252]
                 condition := fun (a : Q(F)) (b : Q(F)) (ρ : Q(F)) => q($ρ = $a * $b) }]

def felt252_is_zero : FuncData where
  inputTypes := [Felt252]
  branches := [
    { outputTypes := []
      condition := fun (a : Q(F)) => q($a = 0) },
    { outputTypes := [Felt252] -- TODO Actually the condition is baked into the output type here
      condition := fun (a ρ : Q(F)) => q($a ≠ 0 ∧ $ρ = $a) }]

def felt252Libfuncs : Identifier → Option FuncData
| .name "felt252_const" [.const n] _ => FuncData.felt252_const q($n)
| .name "felt252_add" []           _ => FuncData.felt252_add
| .name "felt252_sub" []           _ => FuncData.felt252_sub
| .name "felt252_mul" []           _ => FuncData.felt252_mul
| .name "felt252_is_zero" []       _ => FuncData.felt252_is_zero
| _                                  => .none
