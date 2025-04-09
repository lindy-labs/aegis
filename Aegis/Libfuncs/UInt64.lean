import Aegis.Types
import Aegis.Aux.ZMod.DivMod

open Qq Sierra.SierraType

namespace Sierra.FuncData

def u64_overflowing_add : FuncData where
  inputTypes := [RangeCheck, U64, U64]
  branches := [{ outputTypes := [RangeCheck, U64]
                 condition := fun _ (a b : Q(UInt64)) _ (ρ : Q(UInt64)) =>
                   q(¬ BitVec.uaddOverflow $a $b ∧ $ρ = $a + $b) },
               { outputTypes := [RangeCheck, U64]
                 condition := fun _ (a b : Q(UInt64)) _ (ρ : Q(UInt64)) =>
                   q(BitVec.uaddOverflow $a $b ∧ $ρ = $a + $b) }]

def u64_overflowing_sub : FuncData where
  inputTypes := [RangeCheck, U64, U64]
  branches := [{ outputTypes := [RangeCheck, U64]
                 condition := fun _ (a b : Q(UInt64)) _ (ρ : Q(UInt64)) =>
                   q(¬ BitVec.usubOverflow $a $b ∧ $ρ = $a - $b) },
               { outputTypes := [RangeCheck, U64]
                 condition := fun _ (a b : Q(UInt64)) _ (ρ : Q(UInt64)) =>
                   q(BitVec.usubOverflow $a $b ∧ $ρ = $a - $b) }]

def u64_safe_divmod : FuncData where
  inputTypes := [RangeCheck, U64, NonZero U64]
  branches := [{ outputTypes := [RangeCheck, U64, U64]
                 condition := fun _ (a b : Q(UInt64)) _ (ρ_div ρ_mod : Q(UInt64)) =>
                   q($ρ_div = $a / $b ∧ $ρ_mod = $a % $b) }]

def u64_to_felt252 : FuncData where
  inputTypes := [U64]
  branches := [{ outputTypes := [Felt252]
                 condition := fun (a : Q(UInt64)) (ρ : Q(F)) => q($(ρ) = $(a).toNat) }]

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
  branches := [{ condition := fun (a b : Q(UInt64)) => q($a ≠ $b) },
               { condition := fun (a b : Q(UInt64)) => q($a = $b) }]

def u64_try_from_felt252 : FuncData where
  inputTypes := [.RangeCheck, .Felt252]
  branches := [{ outputTypes := [.RangeCheck, .U64]
                 condition := fun _ (a : Q(F)) _ (ρ : Q(UInt64)) =>
                   q($(a).val < U64_MOD ∧ $ρ = $(a).val) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(F)) _ => q(U64_MOD ≤ $(a).val) }]

def u64_wide_mul : FuncData where
  inputTypes := [.U64, .U64]
  branches := [{ outputTypes := [.U128]
                 condition := fun (a b : Q(UInt64)) (ρ : Q(UInt128)) =>
                   q($ρ = $(a).zeroExtend 128 * $(b).zeroExtend 128) }]

def u64_bitwise : FuncData where
  inputTypes := [Bitwise, U64, U64]
  branches := [{ outputTypes := [Bitwise, U64, U64, U64]
                 condition := fun _ (lhs rhs : Q(UInt64)) _ (and xor or : Q(UInt64)) =>
                   q($and = BitVec.and $lhs $rhs ∧ $xor = BitVec.xor $lhs $rhs
                     ∧ $or = BitVec.or $lhs $rhs) }]

def u64_sqrt : FuncData where
  inputTypes := [RangeCheck, U64]
  branches := [{ outputTypes := [RangeCheck, U32]
                 condition := fun _ (a : Q(UInt64)) _ (ρ : Q(UInt32)) => q($ρ = $(a).toNat.sqrt) }]

def uint64Libfuncs : Identifier → Option FuncData
| .name "u64_overflowing_add" [] .none      => u64_overflowing_add
| .name "u64_overflowing_sub" [] .none      => u64_overflowing_sub
| .name "u64_safe_divmod" [] .none          => u64_safe_divmod
| .name "u64_to_felt252" [] .none           => u64_to_felt252
| .name "u64_is_zero" [] .none              => u64_is_zero
| .name "u64_const" [.const n] .none        => u64_const (Lean.toExpr (α := BitVec 64) n)
| .name "u64_eq" [] .none                   => u64_eq
| .name "u64_try_from_felt252" [] .none     => u64_try_from_felt252
| .name "u64_wide_mul" [] .none             => u64_wide_mul
| .name "u64_bitwise" [] .none              => u64_bitwise
| .name "u64_sqrt" [] .none                 => u64_sqrt
| _                                         => .none
