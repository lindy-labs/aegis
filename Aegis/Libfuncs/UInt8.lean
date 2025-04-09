import Aegis.Types
import Aegis.Aux.ZMod.DivMod

open Qq Sierra.SierraType

namespace Sierra.FuncData

def u8_overflowing_add : FuncData where
  inputTypes := [RangeCheck, U8, U8]
  branches := [{ outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(UInt8)) _ (ρ : Q(UInt8)) =>
                   q(¬ BitVec.uaddOverflow $a $b ∧ $ρ = $a + $b) },
               { outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(UInt8)) _ (ρ : Q(UInt8)) =>
                   q(BitVec.uaddOverflow $a $b ∧ $ρ = $a + $b) }]

def u8_overflowing_sub : FuncData where
  inputTypes := [RangeCheck, U8, U8]
  branches := [{ outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(UInt8)) _ (ρ : Q(UInt8)) =>
                   q(¬ BitVec.usubOverflow $a $b ∧ $ρ = $a - $b) },
               { outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(UInt8)) _ (ρ : Q(UInt8)) =>
                   q(BitVec.usubOverflow $a $b ∧ $ρ = $a - $b) }]

def u8_safe_divmod : FuncData where
  inputTypes := [RangeCheck, U8, NonZero U8]
  branches := [{ outputTypes := [RangeCheck, U8, U8]
                 condition := fun _ (a b : Q(UInt8)) _ (ρ_div ρ_mod : Q(UInt8)) =>
                   q($ρ_div = $a / $b ∧ $ρ_mod = $a % $b) }]

def u8_to_felt252 : FuncData where
  inputTypes := [U8]
  branches := [{ outputTypes := [Felt252]
                 condition := fun (a : Q(UInt8)) (ρ : Q(F)) =>
                   q($(ρ) = $(a).toNat) }]

def u8_is_zero : FuncData where
  inputTypes := [U8]
  branches := [{ outputTypes := []
                 condition := fun (a : Q(UInt8)) => q($a = 0) },
               { outputTypes := [NonZero U8]
                 condition := fun (a ρ : Q(UInt8)) => q($a ≠ 0 ∧ $ρ = $a) }]

def u8_const (n : Q(UInt8)) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [U8]
                 condition := fun (ρ : Q(UInt8)) => q($ρ = $n) }]

def u8_eq : FuncData where
  inputTypes := [U8, U8]
  branches := [{ condition := fun (a b : Q(UInt8)) => q($a ≠ $b) },
               { condition := fun (a b : Q(UInt8)) => q($a = $b) }]

def u8_try_from_felt252 : FuncData where
  inputTypes := [.RangeCheck, .Felt252]
  branches := [{ outputTypes := [.RangeCheck, .U8]
                 condition := fun _ (a : Q(F)) _ (ρ : Q(UInt8)) =>
                   q($(a).val < U8_MOD ∧ $ρ = $(a).val) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(F)) _ => q(U8_MOD ≤ $(a).val) }]

def u8_wide_mul : FuncData where
  inputTypes := [.U8, .U8]
  branches := [{ outputTypes := [.U16]
                 condition := fun (a b : Q(UInt8)) (ρ : Q(UInt16)) =>
                   q($ρ = $(a).zeroExtend 16 * $(b).zeroExtend 16) }]

def u8_bitwise : FuncData where
  inputTypes := [Bitwise, U8, U8]
  branches := [{ outputTypes := [Bitwise, U8, U8, U8]
                 condition := fun _ (lhs rhs : Q(UInt8)) _ (and xor or : Q(UInt8)) =>
                   q($and = BitVec.and $lhs $rhs ∧ $xor = BitVec.xor $lhs $rhs
                     ∧ $or = BitVec.or $lhs $rhs) }]

def u8_sqrt : FuncData where
  inputTypes := [RangeCheck, U8]
  branches := [{ outputTypes := [RangeCheck, U8]
                 condition := fun _ (a : Q(UInt8)) _ (ρ : Q(UInt8)) => q($ρ = $(a).toNat.sqrt) }]

def uint8Libfuncs : Identifier → Option FuncData
| .name "u8_overflowing_add" [] .none      => u8_overflowing_add
| .name "u8_overflowing_sub" [] .none      => u8_overflowing_sub
| .name "u8_safe_divmod" [] .none          => u8_safe_divmod
| .name "u8_to_felt252" [] .none           => u8_to_felt252
| .name "u8_is_zero" [] .none              => u8_is_zero
| .name "u8_const" [.const n] .none        => u8_const (Lean.toExpr (α := BitVec 8) n)
| .name "u8_eq" [] .none                   => u8_eq
| .name "u8_try_from_felt252" [] .none     => u8_try_from_felt252
| .name "u8_wide_mul" [] .none             => u8_wide_mul
| .name "u8_bitwise" [] .none              => u8_bitwise
| .name "u8_sqrt" [] .none                 => u8_sqrt
| _                                        => .none
