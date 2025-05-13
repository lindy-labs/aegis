import Aegis.Types
import Mathlib.Data.ZMod.ValMinAbs

open Qq Sierra.SierraType

namespace Sierra.FuncData

def i128_const (n : Q(Int128)): FuncData where
  inputTypes := []
  branches := [{ outputTypes := [I128]
                 condition := fun (ρ : Q(Int128)) => q($ρ = $n) }]

def i128_diff : FuncData where
  inputTypes := [RangeCheck, I128, I128]
  branches := [{ outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(Int128)) _ (ρ : Q(UInt128)) =>
                   q($(b).sle $a ∧ $ρ = $a - $b) },
               { outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(Int128)) _ (ρ : Q(UInt128)) =>
                   q($(a).slt $b ∧ $ρ = $a - $b) }]

def i128_eq : FuncData where
  inputTypes := [I128, I128]
  branches := [{ condition := fun (a b : Q(Int128)) => q($a ≠ $b) },
               { condition := fun (a b : Q(Int128)) => q($a = $b) }]

-- in range / underflow / overflow
def i128_overflowing_add_impl : FuncData where
  inputTypes := [RangeCheck, I128, I128]
  branches := [{ outputTypes := [RangeCheck, I128]
                 condition := fun _ (a b : Q(Int128)) _ (ρ : Q(Int128)) =>
                   q(¬ BitVec.saddOverflow $a $b ∧ $ρ = $a + $b) },
               { outputTypes := [RangeCheck, I128]
                 condition := fun _ (a b : Q(Int128)) _ (ρ : Q(Int128)) =>
                   q(BitVec.saddOverflow $a $b ∧ $ρ = $a + $b) },
               { outputTypes := [RangeCheck, I128]
                 condition := fun _ (a b : Q(Int128)) _ (ρ : Q(Int128)) =>
                   q(BitVec.saddOverflow $a $b ∧ $ρ = $a + $b) }]

def i128_overflowing_sub_impl : FuncData where
  inputTypes := [RangeCheck, I128, I128]
  branches := [{ outputTypes := [RangeCheck, I128]
                 condition := fun _ (a b : Q(Int128)) _ (ρ : Q(Int128)) =>
                   q(¬ BitVec.ssubOverflow $a $b ∧ $ρ = $a - $b) },
               { outputTypes := [RangeCheck, I128]
                 condition := fun _ (a b : Q(Int128)) _ (ρ : Q(Int128)) =>
                   q(BitVec.ssubOverflow $a $b ∧ $ρ = $a - $b) },
               { outputTypes := [RangeCheck, I128]
                 condition := fun _ (a b : Q(Int128)) _ (ρ : Q(Int128)) =>
                   q(BitVec.ssubOverflow $a $b ∧ $ρ = $a - $b) }]

def i128_to_felt252 : FuncData where
  inputTypes := [I128]
  branches := [{ outputTypes := [Felt252]
                 condition := fun (a : Q(Int128)) (ρ : Q(F)) =>
                   q($ρ = $(a).toInt) }]

-- TODO try and find a better behaving axiomatisation
def i128_try_from_felt252 : FuncData where
  inputTypes := [RangeCheck, Felt252]
  branches := [{ outputTypes := [RangeCheck, I128]
                 condition := fun _ (a : Q(F)) _ (ρ : Q(Int128)) =>
                   q(-(2^127) ≤ $(a).valMinAbs ∧ $(a).valMinAbs < 2^127 ∧ $ρ = $(a).valMinAbs) },
               { outputTypes := [RangeCheck]
                 condition := fun _ (a : Q(F)) _ =>
                   q($(a).valMinAbs < -(2^127) ∨ 2^127 ≤ $(a).valMinAbs) }]

def int128Libfuncs : Identifier → Option FuncData
| .name "i128_const" [.const n] .none        => i128_const (Lean.toExpr (α := BitVec 128) n)
| .name "i128_diff" [] .none                 => i128_diff
| .name "i128_eq" [] .none                   => i128_eq
| .name "i128_overflowing_add_impl" [] .none => i128_overflowing_add_impl
| .name "i128_overflowing_sub_impl" [] .none => i128_overflowing_sub_impl
| .name "i128_to_felt252" [] .none           => i128_to_felt252
| .name "i128_try_from_felt252" [] .none     => i128_try_from_felt252
| _                                        => .none
