import Aegis.Types
import Aegis.Aux.ZMod.DivMod
import Aegis.Aux.ZMod.HMul

open Qq Sierra.SierraType

namespace Sierra.FuncData

def u128_overflowing_add : FuncData where
  inputTypes := [RangeCheck, U128, U128]
  branches := [{ outputTypes := [RangeCheck, U128]
                 condition := fun _ (a b : Q(UInt128)) _ (ρ : Q(UInt128)) =>
                   q(($a).val + ($b).val < U128_MOD ∧ $ρ = $a + $b) },
               -- TODO check branch order
               { outputTypes := [RangeCheck, U128]
                 condition := fun _ (a b : Q(UInt128)) _ (ρ : Q(UInt128)) =>
                   q(U128_MOD ≤ ($a).val + ($b).val ∧ $ρ = $a + $b) }]

def u128_overflowing_sub : FuncData where
  inputTypes := [RangeCheck, U128, U128]
  branches := [{ outputTypes := [RangeCheck, U128]
                 condition := fun _ (a b : Q(UInt128)) _ (ρ : Q(UInt128)) =>
                   q(($b).val ≤ ($a).val ∧ $ρ = $a - $b) },
               -- TODO check branch order
               { outputTypes := [RangeCheck, U128]
                 condition := fun _ (a b : Q(UInt128)) _ (ρ : Q(UInt128)) =>
                   q(($a).val < ($b).val ∧ $ρ = $a - $b) }]

def u128_guarantee_mul : FuncData where
  inputTypes := [U128, U128]
  branches := [{ outputTypes := [U128, U128, U128MulGuarantee]
                 condition := fun (a b ρ_high ρ_low : Q(UInt128)) _ =>
                   q($ρ_low = $a * $b ∧ $ρ_high = ZMod.hmul $a $b) }]

def u128_mul_guarantee_verify : FuncData where
  inputTypes := [RangeCheck, U128MulGuarantee]
  branches := [{ outputTypes := [RangeCheck]
                 condition := fun _ _ _ => q(True) }]

def u128s_from_felt252 : FuncData where
  inputTypes := [RangeCheck, Felt252]
  branches := [{ outputTypes := [RangeCheck, U128]
                 condition := fun _ (a : Q(F)) _ (ρ : Q(UInt128)) =>
                   q(($a).val < U128_MOD ∧ $ρ = ($a).cast) },
               { outputTypes := [RangeCheck, U128, U128]
                 condition := fun _ (a : Q(F)) _ (ρ_high ρ_low : Q(UInt128)) =>
                   q(U128_MOD ≤ ($a).val ∧ $ρ_high = $(a).val / U128_MOD
                     ∧ $ρ_low = $(a).cast) }]

def u128_safe_divmod : FuncData where
  inputTypes := [RangeCheck, U128, NonZero U128]
  branches := [{ outputTypes := [RangeCheck, U128, U128]
                 condition := fun _ (a b : Q(UInt128)) _ (ρ_div ρ_mod : Q(UInt128)) =>
                   q($ρ_div = ZMod.ndiv $a $b ∧ $ρ_mod = ZMod.nmod $a $b) }]

def u128_to_felt252 : FuncData where
  inputTypes := [U128]
  branches := [{ outputTypes := [Felt252]
                 condition := fun (a : Q(UInt128)) (ρ : Q(F)) =>
                   q($ρ = $(a).cast) }]

def u128_is_zero : FuncData where
  inputTypes := [U128]
  branches := [{ outputTypes := []
                 condition := fun (a : Q(UInt128)) => q($a = 0) },
               { outputTypes := [NonZero U128]
                 condition := fun (a ρ : Q(UInt128)) => q($a ≠ 0 ∧ $ρ = $a) }]

def u128_const (n : Q(UInt128)) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [U128]
                 condition := fun (ρ : Q(UInt128)) => q($ρ = $n) }]

def u128_eq : FuncData where
  inputTypes := [U128, U128]
  branches := [{ condition := fun (a b : Q(UInt128)) => q($a ≠ $b) },
               { condition := fun (a b : Q(UInt128)) => q($a = $b) }]

def bitwise : FuncData where
  inputTypes := [Bitwise, U128, U128]
  branches := [{ outputTypes := [Bitwise, U128, U128, U128]
                 condition := fun _ (lhs rhs : Q(UInt128)) _ (and xor or : Q(UInt128)) =>
                   q($and = (Nat.land $(lhs).val $(rhs).val).cast
                     ∧ $xor = (Nat.xor $(lhs).val $(rhs).val).cast
                     ∧ $or = (Nat.lor $(lhs).val $(rhs).val).cast) }]

def u128_sqrt : FuncData where
  inputTypes := [RangeCheck, U128]
  branches := [{ outputTypes := [RangeCheck, U64]
                 condition := fun _ (a : Q(UInt128)) _ (ρ : Q(UInt64)) =>
                   q($(ρ).val = $(a).val.sqrt) }]

def uint128Libfuncs : Identifier → Option FuncData
| .name "u128_overflowing_add" [] .none      => u128_overflowing_add
| .name "u128_overflowing_sub" [] .none      => u128_overflowing_sub
| .name "u128_guarantee_mul"   [] .none      => u128_guarantee_mul
| .name "u128_mul_guarantee_verify" [] .none => u128_mul_guarantee_verify
| .name "u128s_from_felt252" [] .none        => u128s_from_felt252
| .name "u128_safe_divmod" [] .none          => u128_safe_divmod
| .name "u128_to_felt252" [] .none           => u128_to_felt252
| .name "u128_is_zero" [] .none              => u128_is_zero
| .name "u128_const" [.const n] .none        => u128_const q($n)
| .name "u128_eq" [] .none                   => u128_eq
| .name "bitwise" [] .none                   => bitwise
| .name "u128_sqrt" [] .none                 => u128_sqrt
| _                                          => .none
