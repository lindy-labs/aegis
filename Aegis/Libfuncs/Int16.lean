import Aegis.Types
import Mathlib.Data.ZMod.ValMinAbs

open Qq Sierra.SierraType

namespace Sierra.FuncData

def i16_const (n : Q(Int16)): FuncData where
  inputTypes := []
  branches := [{ outputTypes := [I16]
                 condition := fun (ρ : Q(Int16)) => q($ρ = $n) }]

def i16_diff : FuncData where
  inputTypes := [RangeCheck, I16, I16]
  branches := [{ outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(Int16)) _ (ρ : Q(UInt16)) =>
                   q($(b).sle $a ∧ $ρ = $a - $b) },
               { outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(Int16)) _ (ρ : Q(UInt16)) =>
                   q($(a).slt $b ∧ $ρ = $a - $b) }]

def i16_eq : FuncData where
  inputTypes := [I16, I16]
  branches := [{ condition := fun (a b : Q(Int16)) => q($a ≠ $b) },
               { condition := fun (a b : Q(Int16)) => q($a = $b) }]

-- in range / underflow / overflow
def i16_overflowing_add_impl : FuncData where
  inputTypes := [RangeCheck, I16, I16]
  branches := [{ outputTypes := [RangeCheck, I16]
                 condition := fun _ (a b : Q(Int16)) _ (ρ : Q(Int16)) =>
                   q(¬ BitVec.saddOverflow $a $b ∧ $ρ = $a + $b) },
               { outputTypes := [RangeCheck, I16]
                 condition := fun _ (a b : Q(Int16)) _ (ρ : Q(Int16)) =>
                   q(BitVec.saddOverflow $a $b ∧ $ρ = $a + $b) },
               { outputTypes := [RangeCheck, I16]
                 condition := fun _ (a b : Q(Int16)) _ (ρ : Q(Int16)) =>
                   q(BitVec.saddOverflow $a $b ∧ $ρ = $a + $b) }]

def i16_overflowing_sub_impl : FuncData where
  inputTypes := [RangeCheck, I16, I16]
  branches := [{ outputTypes := [RangeCheck, I16]
                 condition := fun _ (a b : Q(Int16)) _ (ρ : Q(Int16)) =>
                   q(¬ BitVec.ssubOverflow $a $b ∧ $ρ = $a - $b) },
               { outputTypes := [RangeCheck, I16]
                 condition := fun _ (a b : Q(Int16)) _ (ρ : Q(Int16)) =>
                   q(BitVec.ssubOverflow $a $b ∧ $ρ = $a - $b) },
               { outputTypes := [RangeCheck, I16]
                 condition := fun _ (a b : Q(Int16)) _ (ρ : Q(Int16)) =>
                   q(BitVec.ssubOverflow $a $b ∧ $ρ = $a - $b) }]

def i16_to_felt252 : FuncData where
  inputTypes := [I16]
  branches := [{ outputTypes := [Felt252]
                 condition := fun (a : Q(Int16)) (ρ : Q(F)) =>
                   q($ρ = $(a).toInt) }]

-- TODO try and find a better behaving axiomatisation
def i16_try_from_felt252 : FuncData where
  inputTypes := [RangeCheck, Felt252]
  branches := [{ outputTypes := [RangeCheck, I16]
                 condition := fun _ (a : Q(F)) _ (ρ : Q(Int16)) =>
                   q(-(2^15) ≤ $(a).valMinAbs ∧ $(a).valMinAbs < 2^15 ∧ $ρ = $(a).valMinAbs) },
               { outputTypes := [RangeCheck]
                 condition := fun _ (a : Q(F)) _ =>
                   q($(a).valMinAbs < -(2^15) ∨ 2^15 ≤ $(a).valMinAbs) }]

def i16_wide_mul : FuncData where
  inputTypes := [I16, I16]
  branches := [{ outputTypes := [I32]
                 condition := fun (a b : Q(Int16)) (ρ : Q(Int32)) =>
                   q($ρ = $(a).signExtend 32 * $(b).signExtend 32) }]

def int16Libfuncs : Identifier → Option FuncData
| .name "i16_const" [.const n] .none        => i16_const (Lean.toExpr (α := BitVec 16) n)
| .name "i16_diff" [] .none                 => i16_diff
| .name "i16_eq" [] .none                   => i16_eq
| .name "i16_overflowing_add_impl" [] .none => i16_overflowing_add_impl
| .name "i16_overflowing_sub_impl" [] .none => i16_overflowing_sub_impl
| .name "i16_to_felt252" [] .none           => i16_to_felt252
| .name "i16_try_from_felt252" [] .none     => i16_try_from_felt252
| .name "i16_wide_mul" [] .none             => i16_wide_mul
| _                                        => .none
