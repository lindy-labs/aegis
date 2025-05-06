import Aegis.Types
import Mathlib.Data.ZMod.ValMinAbs

open Qq Sierra.SierraType

namespace Sierra.FuncData

def i64_const (n : Q(Int64)): FuncData where
  inputTypes := []
  branches := [{ outputTypes := [I64]
                 condition := fun (ρ : Q(Int64)) => q($ρ = $n) }]

def i64_diff : FuncData where
  inputTypes := [RangeCheck, I64, I64]
  branches := [{ outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(Int64)) _ (ρ : Q(UInt64)) =>
                   q($(b).sle $a ∧ $ρ = $a - $b) },
               { outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(Int64)) _ (ρ : Q(UInt64)) =>
                   q($(a).slt $b ∧ $ρ = $a - $b) }]

def i64_eq : FuncData where
  inputTypes := [I64, I64]
  branches := [{ condition := fun (a b : Q(Int64)) => q($a ≠ $b) },
               { condition := fun (a b : Q(Int64)) => q($a = $b) }]

-- in range / underflow / overflow
def i64_overflowing_add_impl : FuncData where
  inputTypes := [I64, I64]
  branches := [{ outputTypes := [RangeCheck, I64]
                 condition := fun (a b : Q(Int64)) _ (ρ : Q(Int64)) =>
                   q(¬ BitVec.saddOverflow $a $b ∧ $ρ = $a + $b) },
               { outputTypes := [RangeCheck, I64]
                 condition := fun (a b : Q(Int64)) _ (ρ : Q(Int64)) =>
                   q(BitVec.saddOverflow $a $b ∧ $ρ = $a + $b) },
               { outputTypes := [RangeCheck, I64]
                 condition := fun (a b : Q(Int64)) _ (ρ : Q(Int64)) =>
                   q(BitVec.saddOverflow $a $b ∧ $ρ = $a + $b) }]

def i64_overflowing_sub_impl : FuncData where
  inputTypes := [I64, I64]
  branches := [{ outputTypes := [RangeCheck, I64]
                 condition := fun (a b : Q(Int64)) _ (ρ : Q(Int64)) =>
                   q(¬ BitVec.ssubOverflow $a $b ∧ $ρ = $a - $b) },
               { outputTypes := [RangeCheck, I64]
                 condition := fun (a b : Q(Int64)) _ (ρ : Q(Int64)) =>
                   q(BitVec.ssubOverflow $a $b ∧ $ρ = $a - $b) },
               { outputTypes := [RangeCheck, I64]
                 condition := fun (a b : Q(Int64)) _ (ρ : Q(Int64)) =>
                   q(BitVec.ssubOverflow $a $b ∧ $ρ = $a - $b) }]

def i64_to_felt252 : FuncData where
  inputTypes := [I64]
  branches := [{ outputTypes := [Felt252]
                 condition := fun (a : Q(Int64)) (ρ : Q(F)) =>
                   q($ρ = $(a).toInt) }]

-- TODO try and find a better behaving axiomatisation
def i64_try_from_felt252 : FuncData where
  inputTypes := [RangeCheck, Felt252]
  branches := [{ outputTypes := [RangeCheck, I64]
                 condition := fun _ (a : Q(F)) _ (ρ : Q(Int64)) =>
                   q(-(2^63) ≤ $(a).valMinAbs ∧ $(a).valMinAbs < 2^63 ∧ $ρ = $(a).valMinAbs) },
               { outputTypes := [RangeCheck]
                 condition := fun _ (a : Q(F)) _ =>
                   q($(a).valMinAbs < -(2^63) ∨ 2^63 ≤ $(a).valMinAbs) }]

def i64_wide_mul : FuncData where
  inputTypes := [I64, I64]
  branches := [{ outputTypes := [I128]
                 condition := fun (a b : Q(Int64)) (ρ : Q(Int128)) =>
                   q($ρ = $(a).signExtend 128 * $(b).signExtend 128) }]

def int64Libfuncs : Identifier → Option FuncData
| .name "i64_const" [.const n] .none        => i64_const (Lean.toExpr (α := BitVec 64) n)
| .name "i64_diff" [] .none                 => i64_diff
| .name "i64_eq" [] .none                   => i64_eq
| .name "i64_overflowing_add_impl" [] .none => i64_overflowing_add_impl
| .name "i64_overflowing_sub_impl" [] .none => i64_overflowing_sub_impl
| .name "i64_to_felt252" [] .none           => i64_to_felt252
| .name "i64_try_from_felt252" [] .none     => i64_try_from_felt252
| .name "i64_wide_mul" [] .none             => i64_wide_mul
| _                                        => .none
