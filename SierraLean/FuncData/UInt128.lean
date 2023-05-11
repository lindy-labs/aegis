import SierraLean.FuncDataUtil
import Mathlib.Data.ZMod.Basic

open Qq Sierra.SierraType

namespace Sierra

namespace FuncData

def u128_overflowing_add : FuncData where
  inputTypes := [U128, U128]
  branches := [{ outputTypes := [U128]
                 condition := fun (a b ρ : Q(UInt128)) => q($ρ = $a + $b) }]

def u128_overflowing_sub : FuncData where
  inputTypes := [U128, U128]
  branches := [{ outputTypes := [U128]
                 condition := fun (a b ρ : Q(UInt128)) => q($ρ = $a - $b) }]

def u128_guarantee_mul : FuncData where
  inputTypes := [U128, U128]
  branches := [{ outputTypes := [U128, U128, U128MulGuarantee]
                 condition := fun (a b ρ_high ρ_low : Q(UInt128)) _ =>
                   q(2^128 * ($ρ_high).val + ($ρ_low).val = ($a).val * ($b).val) }]

def u128_mul_guarantee_verify : FuncData where
  inputTypes := [RangeCheck, U128MulGuarantee]
  branches := [{ outputTypes := [RangeCheck]
                 condition := fun _ _ _ => q(True) }]

def u128s_from_felt252 : FuncData where
  inputTypes := [RangeCheck, Felt252]
  branches := [{ outputTypes := [RangeCheck, U128]
                 condition := fun _ (a : Q(F)) _ (ρ : Q(UInt128)) =>
                   q(($ρ).val = ($a).val) },
               { outputTypes := [RangeCheck, U128, U128]
                 -- TODO check that `ρ_high` and `ρ_low` are really in the correct order
                 condition := fun _ (a : Q(F)) _ (ρ_high ρ_low : Q(UInt128)) =>
                   q(2^128 * ($ρ_high).val + ($ρ_low).val = ($a).val) }]

def u128_safe_divmod : FuncData where
  inputTypes := [RangeCheck, U128, NonZero U128]
  branches := [{ outputTypes := [RangeCheck, U128, U128]
                 condition := fun _ (a b : Q(UInt128)) _ (ρ_div ρ_mod : Q(UInt128)) =>
                   q($(a).val = $(b).val * $(ρ_div).val + $(ρ_mod).val) }]

def u128_to_felt252 : FuncData where
  inputTypes := [U128]
  branches := [{ outputTypes := [Felt252]
                 condition := fun (a : Q(UInt128)) (ρ : Q(F)) =>
                   q($(ρ).val = $(a).val) }]

def u128_is_zero : FuncData where
  inputTypes := [U128]
  branches := [{ outputTypes := []
                 condition := fun (a : Q(UInt128)) => q($a = 0) },
               { outputTypes := [NonZero U128]
                 condition := fun (a ρ : Q(UInt128)) => q($ρ = $a) }]

def uint128Libfuncs : Identifier → Option FuncData
| .name "u128_overflowing_add" [] .none      => u128_overflowing_add
| .name "u128_overflowing_sub" [] .none      => u128_overflowing_sub
| .name "u128_guarantee_mul"   [] .none      => u128_guarantee_mul
| .name "u128_mul_guarantee_verify" [] .none => u128_mul_guarantee_verify
| .name "u128s_from_felt252" [] .none        => u128s_from_felt252
| .name "u128_safe_divmod" [] .none          => u128_safe_divmod
| .name "u128_to_felt252" [] .none           => u128_to_felt252
| .name "u128_is_zero" [] .none              => u128_is_zero
| _                                          => .none
