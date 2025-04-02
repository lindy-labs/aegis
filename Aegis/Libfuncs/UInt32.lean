import Aegis.Types
import Aegis.Aux.ZMod.DivMod

open Qq Sierra.SierraType

namespace Sierra.FuncData

def u32_overflowing_add : FuncData where
  inputTypes := [RangeCheck, U32, U32]
  branches := [{ outputTypes := [RangeCheck, U32]
                 condition := fun _ (a b : Q(UInt32)) _ (ρ : Q(UInt32)) =>
                   q(($a).toNat + ($b).toNat < U32_MOD ∧ $ρ = $a + $b) },
               { outputTypes := [RangeCheck, U32]
                 condition := fun _ (a b : Q(UInt32)) _ (ρ : Q(UInt32)) =>
                   q(U32_MOD ≤ ($a).toNat + ($b).toNat ∧ $ρ = $a + $b) }]

def u32_overflowing_sub : FuncData where
  inputTypes := [RangeCheck, U32, U32]
  branches := [{ outputTypes := [RangeCheck, U32]
                 condition := fun _ (a b : Q(UInt32)) _ (ρ : Q(UInt32)) =>
                   q($b ≤ $a ∧ $ρ = $a - $b) },
               { outputTypes := [RangeCheck, U32]
                 condition := fun _ (a b : Q(UInt32)) _ (ρ : Q(UInt32)) =>
                   q($a < $b ∧ $ρ = $a - $b) }]

def u32_safe_divmod : FuncData where
  inputTypes := [RangeCheck, U32, NonZero U32]
  branches := [{ outputTypes := [RangeCheck, U32, U32]
                 condition := fun _ (a b : Q(UInt32)) _ (ρ_div ρ_mod : Q(UInt32)) =>
                   q($ρ_div = $a / $b ∧ $ρ_mod = $a % $b) }]

def u32_to_felt252 : FuncData where
  inputTypes := [U32]
  branches := [{ outputTypes := [Felt252]
                 condition := fun (a : Q(UInt32)) (ρ : Q(F)) =>
                   q($(ρ) = Fin.castLE (Nat.le_add_left (2 ^ 32) 3618502788666131213697322783095070105623107215331596699973092056131577053185) $(a).toFin) }]

example (x : Fin 8) (h : x.castLE (by simp) = (0 : Fin 13)) : x = 0 := by
  rwa [← Fin.castLE_zero (n := 7) (m := 12) (by simp), Fin.castLE_inj] at h

def u32_is_zero : FuncData where
  inputTypes := [U32]
  branches := [{ outputTypes := []
                 condition := fun (a : Q(UInt32)) => q($a = 0) },
               { outputTypes := [NonZero U32]
                 condition := fun (a ρ : Q(UInt32)) => q($a ≠ 0 ∧ $ρ = $a) }]

def u32_const (n : Q(UInt32)) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [U32]
                 condition := fun (ρ : Q(UInt32)) => q($ρ = $n) }]

def u32_eq : FuncData where
  inputTypes := [U32, U32]
  branches := [{ condition := fun (a b : Q(UInt32)) => q($a ≠ $b) },
               { condition := fun (a b : Q(UInt32)) => q($a = $b) }]

def u32_try_from_felt252 : FuncData where
  inputTypes := [.RangeCheck, .Felt252]
  branches := [{ outputTypes := [.RangeCheck, .U32]
                 condition := fun _ (a : Q(F)) _ (ρ : Q(UInt32)) =>
                   q($(a).val < U32_MOD ∧ $ρ = BitVec.ofNat _ $(a).val) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(F)) _ => q(U32_MOD ≤ $(a).val) }]

def u32_wide_mul : FuncData where
  inputTypes := [.U32, .U32]
  branches := [{ outputTypes := [.U64]
                 condition := fun (a b : Q(UInt32)) (ρ : Q(UInt64)) =>
                   q($ρ = $(a).zeroExtend 64 * $(b).zeroExtend 64) }]

def u32_bitwise : FuncData where
  inputTypes := [Bitwise, U32, U32]
  branches := [{ outputTypes := [Bitwise, U32, U32, U32]
                 condition := fun _ (lhs rhs : Q(UInt32)) _ (and xor or : Q(UInt32)) =>
                   q($and = BitVec.and $lhs $rhs ∧ $xor = BitVec.xor $lhs $rhs
                     ∧ $or = BitVec.or $lhs $rhs) }]

def u32_sqrt : FuncData where
  inputTypes := [RangeCheck, U32]
  branches := [{ outputTypes := [RangeCheck, U16]
                 condition := fun _ (a : Q(UInt32)) _ (ρ : Q(UInt16)) => q($ρ = $(a).toNat.sqrt) }]

def uint32Libfuncs : Identifier → Option FuncData
| .name "u32_overflowing_add" [] .none      => u32_overflowing_add
| .name "u32_overflowing_sub" [] .none      => u32_overflowing_sub
| .name "u32_safe_divmod" [] .none          => u32_safe_divmod
| .name "u32_to_felt252" [] .none           => u32_to_felt252
| .name "u32_is_zero" [] .none              => u32_is_zero
| .name "u32_const" [.const n] .none        => u32_const q($n)
| .name "u32_eq" [] .none                   => u32_eq
| .name "u32_try_from_felt252" [] .none     => u32_try_from_felt252
| .name "u32_wide_mul" [] .none             => u32_wide_mul
| .name "u32_bitwise" [] .none              => u32_bitwise
| .name "u32_sqrt" [] .none                 => u32_sqrt
| _                                         => .none
