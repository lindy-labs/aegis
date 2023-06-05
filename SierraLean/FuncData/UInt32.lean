import SierraLean.FuncDataUtil
import Mathlib.Data.ZMod.Basic

open Qq Sierra.SierraType

namespace Sierra.FuncData

def u32_overflowing_add : FuncData where
  inputTypes := [RangeCheck, U32, U32]
  branches := [{ outputTypes := [RangeCheck, U32]
                 condition := fun _ (a b : Q(UInt32)) _ (ρ : Q(UInt32)) => 
                   q(($a).val + ($b).val < 2^32 ∧ $ρ = $a + $b) },
               -- TODO check branch order
               { outputTypes := [RangeCheck, U32]
                 condition := fun _ (a b : Q(UInt32)) _ (ρ : Q(UInt32)) =>
                   q(($a).val + ($b).val ≥ 2^32 ∧ $ρ = $a + $b) }]

def u32_overflowing_sub : FuncData where
  inputTypes := [RangeCheck, U32, U32]
  branches := [{ outputTypes := [RangeCheck, U32]
                 condition := fun _ (a b : Q(UInt32)) _ (ρ : Q(UInt32)) => 
                   q(($a).val ≥ ($b).val ∧ $ρ = $a - $b) },
               -- TODO check branch order
               { outputTypes := [RangeCheck, U32]
                 condition := fun _ (a b : Q(UInt32)) _ (ρ : Q(UInt32)) =>
                   q(($a).val < ($b).val ∧ $ρ = $a - $b) }]

def u32s_from_felt252 : FuncData where
  inputTypes := [RangeCheck, Felt252]
  branches := [{ outputTypes := [RangeCheck, U32]
                 condition := fun _ (a : Q(F)) _ (ρ : Q(UInt32)) =>
                   q(($ρ).val = ($a).val) },
               { outputTypes := [RangeCheck, U32, U32]
                 -- TODO check that `ρ_high` and `ρ_low` are really in the correct order
                 condition := fun _ (a : Q(F)) _ (ρ_high ρ_low : Q(UInt32)) =>
                   q(2^32 * ($ρ_high).val + ($ρ_low).val = ($a).val) }]

def u32_safe_divmod : FuncData where
  inputTypes := [RangeCheck, U32, NonZero U32]
  branches := [{ outputTypes := [RangeCheck, U32, U32]
                 condition := fun _ (a b : Q(UInt32)) _ (ρ_div ρ_mod : Q(UInt32)) =>
                   q($(a).val = $(b).val * $(ρ_div).val + $(ρ_mod).val
                     ∧ $(ρ_mod).val < $(b).val) }]

def u32_to_felt252 : FuncData where
  inputTypes := [U32]
  branches := [{ outputTypes := [Felt252]
                 condition := fun (a : Q(UInt32)) (ρ : Q(F)) =>
                   q($(ρ).val = $(a).val) }]

def u32_is_zero : FuncData where
  inputTypes := [U32]
  branches := [{ outputTypes := []
                 condition := fun (a : Q(UInt32)) => q($a = 0) },
               { outputTypes := [NonZero U32]
                 condition := fun (a ρ : Q(UInt32)) => q($ρ = $a) }]

def u32_const (n : Q(UInt32)) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [U32]
                 condition := fun (ρ : Q(UInt32)) => q($ρ = $n) }]

def u32_eq : FuncData where
  inputTypes := [U32, U32]
  -- TODO double check the order of branches
  branches := [{ condition := fun (a b : Q(UInt32)) => q($a ≠ $b) },
               { condition := fun (a b : Q(UInt32)) => q($a = $b) }]

def uint32Libfuncs : Identifier → Option FuncData
| .name "u32_overflowing_add" [] .none      => u32_overflowing_add
| .name "u32_overflowing_sub" [] .none      => u32_overflowing_sub
| .name "u32s_from_felt252" [] .none        => u32s_from_felt252
| .name "u32_safe_divmod" [] .none          => u32_safe_divmod
| .name "u32_to_felt252" [] .none           => u32_to_felt252
| .name "u32_is_zero" [] .none              => u32_is_zero
| .name "u32_const" [.const n] .none        => u32_const q($n)
| .name "u32_eq" [] .none                   => u32_eq
| _                                         => .none
