import Aegis.Types
import Mathlib.Data.ZMod.ValMinAbs

open Qq Sierra.SierraType

namespace Sierra.FuncData

def i32_const (n : Q(Int32)): FuncData where
  inputTypes := []
  branches := [{ outputTypes := [I32]
                 condition := fun (ρ : Q(Int32)) => q($ρ = $n) }]

def i32_diff : FuncData where
  inputTypes := [RangeCheck, I32, I32]
  branches := [{ outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(Int32)) _ (ρ : Q(UInt32)) =>
                   q($(b).sle $a ∧ $ρ = $a - $b) },
               { outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(Int32)) _ (ρ : Q(UInt32)) =>
                   q($(a).slt $b ∧ $ρ = $a - $b) }]

def i32_eq : FuncData where
  inputTypes := [I32, I32]
  branches := [{ condition := fun (a b : Q(Int32)) => q($a ≠ $b) },
               { condition := fun (a b : Q(Int32)) => q($a = $b) }]

-- in range / underflow / overflow
def i32_overflowing_add_impl : FuncData where
  inputTypes := [I32, I32]
  branches := [{ outputTypes := [RangeCheck, I32]
                 condition := fun (a b : Q(Int32)) _ (ρ : Q(Int32)) =>
                   q(¬ BitVec.saddOverflow $a $b ∧ $ρ = $a + $b) },
               { outputTypes := [RangeCheck, I32]
                 condition := fun (a b : Q(Int32)) _ (ρ : Q(Int32)) =>
                   q(BitVec.saddOverflow $a $b ∧ $ρ = $a + $b) },
               { outputTypes := [RangeCheck, I32]
                 condition := fun (a b : Q(Int32)) _ (ρ : Q(Int32)) =>
                   q(BitVec.saddOverflow $a $b ∧ $ρ = $a + $b) }]

def i32_overflowing_sub_impl : FuncData where
  inputTypes := [I32, I32]
  branches := [{ outputTypes := [RangeCheck, I32]
                 condition := fun (a b : Q(Int32)) _ (ρ : Q(Int32)) =>
                   q(¬ BitVec.ssubOverflow $a $b ∧ $ρ = $a - $b) },
               { outputTypes := [RangeCheck, I32]
                 condition := fun (a b : Q(Int32)) _ (ρ : Q(Int32)) =>
                   q(BitVec.ssubOverflow $a $b ∧ $ρ = $a - $b) },
               { outputTypes := [RangeCheck, I32]
                 condition := fun (a b : Q(Int32)) _ (ρ : Q(Int32)) =>
                   q(BitVec.ssubOverflow $a $b ∧ $ρ = $a - $b) }]

def i32_to_felt252 : FuncData where
  inputTypes := [I32]
  branches := [{ outputTypes := [Felt252]
                 condition := fun (a : Q(Int32)) (ρ : Q(F)) =>
                   q($ρ = $(a).toInt) }]

-- TODO try and find a better behaving axiomatisation
def i32_try_from_felt252 : FuncData where
  inputTypes := [RangeCheck, Felt252]
  branches := [{ outputTypes := [RangeCheck, I32]
                 condition := fun _ (a : Q(F)) _ (ρ : Q(Int32)) =>
                   q(-(2^31) ≤ $(a).valMinAbs ∧ $(a).valMinAbs < 2^31 ∧ $ρ = $(a).valMinAbs) },
               { outputTypes := [RangeCheck]
                 condition := fun _ (a : Q(F)) _ =>
                   q($(a).valMinAbs < -(2^31) ∨ 2^31 ≤ $(a).valMinAbs) }]

def i32_wide_mul : FuncData where
  inputTypes := [I32, I32]
  branches := [{ outputTypes := [I64]
                 condition := fun (a b : Q(Int32)) (ρ : Q(Int64)) =>
                   q($ρ = $(a).signExtend 64 * $(b).signExtend 64) }]

def int32Libfuncs : Identifier → Option FuncData
| .name "i32_const" [.const n] .none        => i32_const (Lean.toExpr (α := BitVec 32) n)
| .name "i32_diff" [] .none                 => i32_diff
| .name "i32_eq" [] .none                   => i32_eq
| .name "i32_overflowing_add_impl" [] .none => i32_overflowing_add_impl
| .name "i32_overflowing_sub_impl" [] .none => i32_overflowing_sub_impl
| .name "i32_to_felt252" [] .none           => i32_to_felt252
| .name "i32_try_from_felt252" [] .none     => i32_try_from_felt252
| .name "i32_wide_mul" [] .none             => i32_wide_mul
| _                                        => .none
