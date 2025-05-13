import Aegis.Types
import Mathlib.Data.ZMod.ValMinAbs

open Qq Sierra.SierraType

namespace Sierra.FuncData

def i8_const (n : Q(Int8)): FuncData where
  inputTypes := []
  branches := [{ outputTypes := [I8]
                 condition := fun (ρ : Q(Int8)) => q($ρ = $n) }]

def i8_diff : FuncData where
  inputTypes := [RangeCheck, I8, I8]
  branches := [{ outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(Int8)) _ (ρ : Q(UInt8)) =>
                   q($(b).sle $a ∧ $ρ = $a - $b) },
               { outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(Int8)) _ (ρ : Q(UInt8)) =>
                   q($(a).slt $b ∧ $ρ = $a - $b) }]

def i8_eq : FuncData where
  inputTypes := [I8, I8]
  branches := [{ condition := fun (a b : Q(Int8)) => q($a ≠ $b) },
               { condition := fun (a b : Q(Int8)) => q($a = $b) }]

-- in range / underflow / overflow
def i8_overflowing_add_impl : FuncData where
  inputTypes := [RangeCheck, I8, I8]
  branches := [{ outputTypes := [RangeCheck, I8]
                 condition := fun _ (a b : Q(Int8)) _ (ρ : Q(Int8)) =>
                   q(¬ BitVec.saddOverflow $a $b ∧ $ρ = $a + $b) },
               { outputTypes := [RangeCheck, I8]
                 condition := fun _ (a b : Q(Int8)) _ (ρ : Q(Int8)) =>
                   q(BitVec.saddOverflow $a $b ∧ $ρ = $a + $b) },
               { outputTypes := [RangeCheck, I8]
                 condition := fun _ (a b : Q(Int8)) _ (ρ : Q(Int8)) =>
                   q(BitVec.saddOverflow $a $b ∧ $ρ = $a + $b) }]

def i8_overflowing_sub_impl : FuncData where
  inputTypes := [RangeCheck, I8, I8]
  branches := [{ outputTypes := [RangeCheck, I8]
                 condition := fun _ (a b : Q(Int8)) _ (ρ : Q(Int8)) =>
                   q(¬ BitVec.ssubOverflow $a $b ∧ $ρ = $a - $b) },
               { outputTypes := [RangeCheck, I8]
                 condition := fun _ (a b : Q(Int8)) _ (ρ : Q(Int8)) =>
                   q(BitVec.ssubOverflow $a $b ∧ $ρ = $a - $b) },
               { outputTypes := [RangeCheck, I8]
                 condition := fun _ (a b : Q(Int8)) _ (ρ : Q(Int8)) =>
                   q(BitVec.ssubOverflow $a $b ∧ $ρ = $a - $b) }]

def i8_to_felt252 : FuncData where
  inputTypes := [I8]
  branches := [{ outputTypes := [Felt252]
                 condition := fun (a : Q(Int8)) (ρ : Q(F)) =>
                   q($ρ = $(a).toInt) }]

-- TODO try and find a better behaving axiomatisation
def i8_try_from_felt252 : FuncData where
  inputTypes := [RangeCheck, Felt252]
  branches := [{ outputTypes := [RangeCheck, I8]
                 condition := fun _ (a : Q(F)) _ (ρ : Q(Int8)) =>
                   q(-(2^7) ≤ $(a).valMinAbs ∧ $(a).valMinAbs < 2^7 ∧ $ρ = $(a).valMinAbs) },
               { outputTypes := [RangeCheck]
                 condition := fun _ (a : Q(F)) _ =>
                   q($(a).valMinAbs < -(2^7) ∨ 2^7 ≤ $(a).valMinAbs) }]

def i8_wide_mul : FuncData where
  inputTypes := [I8, I8]
  branches := [{ outputTypes := [I16]
                 condition := fun (a b : Q(Int8)) (ρ : Q(Int16)) =>
                   q($ρ = $(a).signExtend 16 * $(b).signExtend 16) }]

def int8Libfuncs : Identifier → Option FuncData
| .name "i8_const" [.const n] .none        => i8_const (Lean.toExpr (α := BitVec 8) n)
| .name "i8_diff" [] .none                 => i8_diff
| .name "i8_eq" [] .none                   => i8_eq
| .name "i8_overflowing_add_impl" [] .none => i8_overflowing_add_impl
| .name "i8_overflowing_sub_impl" [] .none => i8_overflowing_sub_impl
| .name "i8_to_felt252" [] .none           => i8_to_felt252
| .name "i8_try_from_felt252" [] .none     => i8_try_from_felt252
| .name "i8_wide_mul" [] .none             => i8_wide_mul
| _                                        => .none
