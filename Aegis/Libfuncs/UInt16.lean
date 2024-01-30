import Aegis.Types
import Aegis.Aux.ZMod.DivMod

open Qq Sierra.SierraType

namespace Sierra.FuncData

def u16_overflowing_add : FuncData where
  inputTypes := [RangeCheck, U16, U16]
  branches := [{ outputTypes := [RangeCheck, U16]
                 condition := fun _ (a b : Q(UInt16)) _ (ρ : Q(UInt16)) =>
                   q(($a).val + ($b).val < U16_MOD ∧ $ρ = $a + $b) },
               -- TODO check branch order
               { outputTypes := [RangeCheck, U16]
                 condition := fun _ (a b : Q(UInt16)) _ (ρ : Q(UInt16)) =>
                   q(U16_MOD ≤ ($a).val + ($b).val ∧ $ρ = $a + $b) }]

def u16_overflowing_sub : FuncData where
  inputTypes := [RangeCheck, U16, U16]
  branches := [{ outputTypes := [RangeCheck, U16]
                 condition := fun _ (a b : Q(UInt16)) _ (ρ : Q(UInt16)) =>
                   q(($b).val ≤ ($a).val ∧ $ρ = $a - $b) },
               -- TODO check branch order
               { outputTypes := [RangeCheck, U16]
                 condition := fun _ (a b : Q(UInt16)) _ (ρ : Q(UInt16)) =>
                   q(($a).val < ($b).val ∧ $ρ = $a - $b) }]

def u16s_from_felt252 : FuncData where
  inputTypes := [RangeCheck, Felt252]
  branches := [{ outputTypes := [RangeCheck, U16]
                 condition := fun _ (a : Q(F)) _ (ρ : Q(UInt16)) =>
                   q(($ρ).val = ($a).val) },
               { outputTypes := [RangeCheck, U16, U16]
                 -- TODO check that `ρ_high` and `ρ_low` are really in the correct order
                 condition := fun _ (a : Q(F)) _ (ρ_high ρ_low : Q(UInt16)) =>
                   q(U16_MOD * ($ρ_high).val + ($ρ_low).val = ($a).val) }]

def u16_safe_divmod : FuncData where
  inputTypes := [RangeCheck, U16, NonZero U16]
  branches := [{ outputTypes := [RangeCheck, U16, U16]
                 condition := fun _ (a b : Q(UInt16)) _ (ρ_div ρ_mod : Q(UInt16)) =>
                   q($ρ_div = ZMod.ndiv $a $b ∧ $ρ_mod = ZMod.nmod $a $b) }]

def u16_to_felt252 : FuncData where
  inputTypes := [U16]
  branches := [{ outputTypes := [Felt252]
                 condition := fun (a : Q(UInt16)) (ρ : Q(F)) =>
                   q($(ρ) = $(a).cast) }]

def u16_is_zero : FuncData where
  inputTypes := [U16]
  branches := [{ outputTypes := []
                 condition := fun (a : Q(UInt16)) => q($a = 0) },
               { outputTypes := [NonZero U16]
                 condition := fun (a ρ : Q(UInt16)) => q($a ≠ 0 ∧ $ρ = $a) }]

def u16_const (n : Q(UInt16)) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [U16]
                 condition := fun (ρ : Q(UInt16)) => q($ρ = $n) }]

def u16_eq : FuncData where
  inputTypes := [U16, U16]
  -- TODO double check the order of branches
  branches := [{ condition := fun (a b : Q(UInt16)) => q($a ≠ $b) },
               { condition := fun (a b : Q(UInt16)) => q($a = $b) }]

def u16_try_from_felt252 : FuncData where
  inputTypes := [.RangeCheck, .Felt252]
  branches := [{ outputTypes := [.RangeCheck, .U16]
                 condition := fun _ (a : Q(F)) _ (ρ : Q(UInt16)) =>
                   q($(a).val < U16_MOD ∧ $ρ = $(a).cast) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(F)) _ => q(U16_MOD ≤ $(a).val) }]

def u16_wide_mul : FuncData where
  inputTypes := [.U16, .U16]
  branches := [{ outputTypes := [.U32]
                 condition := fun (a b : Q(UInt16)) (ρ : Q(UInt32)) =>
                   q($ρ = $(a).cast * $(b).cast) }]

def uint16Libfuncs : Identifier → Option FuncData
| .name "u16_overflowing_add" [] .none      => u16_overflowing_add
| .name "u16_overflowing_sub" [] .none      => u16_overflowing_sub
| .name "u16s_from_felt252" [] .none        => u16s_from_felt252
| .name "u16_safe_divmod" [] .none          => u16_safe_divmod
| .name "u16_to_felt252" [] .none           => u16_to_felt252
| .name "u16_is_zero" [] .none              => u16_is_zero
| .name "u16_const" [.const n] .none        => u16_const q($n)
| .name "u16_eq" [] .none                   => u16_eq
| .name "u16_try_from_felt252" [] .none     => u16_try_from_felt252
| .name "u16_wide_mul" [] .none             => u16_wide_mul
| _                                         => .none
