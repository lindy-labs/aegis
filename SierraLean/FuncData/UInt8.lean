import SierraLean.FuncDataUtil
import Mathlib.Data.ZMod.Basic

open Qq Sierra.SierraType

namespace Sierra.FuncData

def u8_overflowing_add : FuncData where
  inputTypes := [RangeCheck, U8, U8]
  branches := [{ outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(UInt8)) _ (ρ : Q(UInt8)) => 
                   q(($a).val + ($b).val < 2^8 ∧ $ρ = $a + $b) },
               -- TODO check branch order
               { outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(UInt8)) _ (ρ : Q(UInt8)) =>
                   q(($a).val + ($b).val ≥ 2^8 ∧ $ρ = $a + $b) }]

def u8_overflowing_sub : FuncData where
  inputTypes := [RangeCheck, U8, U8]
  branches := [{ outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(UInt8)) _ (ρ : Q(UInt8)) => 
                   q(($a).val ≥ ($b).val ∧ $ρ = $a - $b) },
               -- TODO check branch order
               { outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(UInt8)) _ (ρ : Q(UInt8)) =>
                   q(($a).val < ($b).val ∧ $ρ = $a - $b) }]

def u8s_from_felt252 : FuncData where
  inputTypes := [RangeCheck, Felt252]
  branches := [{ outputTypes := [RangeCheck, U8]
                 condition := fun _ (a : Q(F)) _ (ρ : Q(UInt8)) =>
                   q(($ρ).val = ($a).val) },
               { outputTypes := [RangeCheck, U8, U8]
                 -- TODO check that `ρ_high` and `ρ_low` are really in the correct order
                 condition := fun _ (a : Q(F)) _ (ρ_high ρ_low : Q(UInt8)) =>
                   q(2^8 * ($ρ_high).val + ($ρ_low).val = ($a).val) }]

def u8_safe_divmod : FuncData where
  inputTypes := [RangeCheck, U8, NonZero U8]
  branches := [{ outputTypes := [RangeCheck, U8, U8]
                 condition := fun _ (a b : Q(UInt8)) _ (ρ_div ρ_mod : Q(UInt8)) =>
                   q($(a).val = $(b).val * $(ρ_div).val + $(ρ_mod).val
                     ∧ $(ρ_mod).val < $(b).val) }]

def u8_to_felt252 : FuncData where
  inputTypes := [U8]
  branches := [{ outputTypes := [Felt252]
                 condition := fun (a : Q(UInt8)) (ρ : Q(F)) =>
                   q($(ρ).val = $(a).val) }]

def u8_is_zero : FuncData where
  inputTypes := [U8]
  branches := [{ outputTypes := []
                 condition := fun (a : Q(UInt8)) => q($a = 0) },
               { outputTypes := [NonZero U8]
                 condition := fun (a ρ : Q(UInt8)) => q($ρ = $a) }]

def u8_const (n : Q(UInt8)) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [U8]
                 condition := fun (ρ : Q(UInt8)) => q($ρ = $n) }]

def u8_eq : FuncData where
  inputTypes := [U8, U8]
  -- TODO double check the order of branches
  branches := [{ condition := fun (a b : Q(UInt8)) => q($a ≠ $b) },
               { condition := fun (a b : Q(UInt8)) => q($a = $b) }]

def uint8Libfuncs : Identifier → Option FuncData
| .name "u8_overflowing_add" [] .none      => u8_overflowing_add
| .name "u8_overflowing_sub" [] .none      => u8_overflowing_sub
| .name "u8s_from_felt252" [] .none        => u8s_from_felt252
| .name "u8_safe_divmod" [] .none          => u8_safe_divmod
| .name "u8_to_felt252" [] .none           => u8_to_felt252
| .name "u8_is_zero" [] .none              => u8_is_zero
| .name "u8_const" [.const n] .none        => u8_const q($n)
| .name "u8_eq" [] .none                   => u8_eq
| _                                         => .none
