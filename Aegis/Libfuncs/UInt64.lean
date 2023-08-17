import Aegis.Types
import Aegis.Aux.ZMod.DivMod

open Qq Sierra.SierraType

namespace Sierra.FuncData

def u64_overflowing_add : FuncData where
  inputTypes := [RangeCheck, U64, U64]
  branches := [{ outputTypes := [RangeCheck, U64]
                 condition := fun _ (a b : Q(UInt64)) _ (ρ : Q(UInt64)) => 
                   q(($a).val + ($b).val < U64_MOD ∧ $ρ = $a + $b) },
               -- TODO check branch order
               { outputTypes := [RangeCheck, U64]
                 condition := fun _ (a b : Q(UInt64)) _ (ρ : Q(UInt64)) =>
                   q(U64_MOD ≤ ($a).val + ($b).val ∧ $ρ = $a + $b) }]

def u64_overflowing_sub : FuncData where
  inputTypes := [RangeCheck, U64, U64]
  branches := [{ outputTypes := [RangeCheck, U64]
                 condition := fun _ (a b : Q(UInt64)) _ (ρ : Q(UInt64)) => 
                   q(($b).val ≤ ($a).val ∧ $ρ = $a - $b) },
               -- TODO check branch order
               { outputTypes := [RangeCheck, U64]
                 condition := fun _ (a b : Q(UInt64)) _ (ρ : Q(UInt64)) =>
                   q(($a).val < ($b).val ∧ $ρ = $a - $b) }]

def u64s_from_felt252 : FuncData where
  inputTypes := [RangeCheck, Felt252]
  branches := [{ outputTypes := [RangeCheck, U64]
                 condition := fun _ (a : Q(F)) _ (ρ : Q(UInt64)) =>
                   q(($ρ).val = ($a).val) },
               { outputTypes := [RangeCheck, U64, U64]
                 -- TODO check that `ρ_high` and `ρ_low` are really in the correct order
                 condition := fun _ (a : Q(F)) _ (ρ_high ρ_low : Q(UInt64)) =>
                   q(U64_MOD * ($ρ_high).val + ($ρ_low).val = ($a).val) }]

def u64_safe_divmod : FuncData where
  inputTypes := [RangeCheck, U64, NonZero U64]
  branches := [{ outputTypes := [RangeCheck, U64, U64]
                 condition := fun _ (a b : Q(UInt64)) _ (ρ_div ρ_mod : Q(UInt64)) =>
                   q($ρ_div = ZMod.ndiv $a $b ∧ $ρ_mod = ZMod.nmod $a $b) }]

def u64_to_felt252 : FuncData where
  inputTypes := [U64]
  branches := [{ outputTypes := [Felt252]
                 condition := fun (a : Q(UInt64)) (ρ : Q(F)) =>
                   q($(ρ) = $(a).cast) }]

def u64_is_zero : FuncData where
  inputTypes := [U64]
  branches := [{ outputTypes := []
                 condition := fun (a : Q(UInt64)) => q($a = 0) },
               { outputTypes := [NonZero U64]
                 condition := fun (a ρ : Q(UInt64)) => q($a ≠ 0 ∧ $ρ = $a) }]

def u64_const (n : Q(UInt64)) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [U64]
                 condition := fun (ρ : Q(UInt64)) => q($ρ = $n) }]

def u64_eq : FuncData where
  inputTypes := [U64, U64]
  -- TODO double check the order of branches
  branches := [{ condition := fun (a b : Q(UInt64)) => q($a ≠ $b) },
               { condition := fun (a b : Q(UInt64)) => q($a = $b) }]

def u64_try_from_felt252 : FuncData where
  inputTypes := [.RangeCheck, .Felt252]
  branches := [{ outputTypes := [.RangeCheck, .U64]
                 condition := fun _ (a : Q(F)) _ (ρ : Q(UInt64)) => 
                   q($(a).val < U64_MOD ∧ $ρ = $(a).cast) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(F)) _ => q(U64_MOD ≤ $(a).val) }]

def uint64Libfuncs : Identifier → Option FuncData
| .name "u64_overflowing_add" [] .none      => u64_overflowing_add
| .name "u64_overflowing_sub" [] .none      => u64_overflowing_sub
| .name "u64s_from_felt252" [] .none        => u64s_from_felt252
| .name "u64_safe_divmod" [] .none          => u64_safe_divmod
| .name "u64_to_felt252" [] .none           => u64_to_felt252
| .name "u64_is_zero" [] .none              => u64_is_zero
| .name "u64_const" [.const n] .none        => u64_const q($n)
| .name "u64_eq" [] .none                   => u64_eq
| .name "u64_try_from_felt252" [] .none     => u64_try_from_felt252
| _                                         => .none
