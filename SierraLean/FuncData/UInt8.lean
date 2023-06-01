import SierraLean.FuncDataUtil
import Mathlib.Data.ZMod.Basic

open Qq Sierra.SierraType

namespace Sierra.FuncData

def u8_overflowing_add : FuncData where
  inputTypes := [RangeCheck, U8, U8]
  branches := [{ outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(UInt8)) _ (ρ : Q(UInt8)) => 
                   q(($a).val + ($b).val < 2^8 ∧ $ρ = $a + $b) },
               -- TODO check branch order
               { outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(UInt8)) _ (ρ : Q(UInt8)) =>
                   q(($a).val + ($b).val ≥ 2^8 ∧ $ρ = $a + $b) }]

def u8_overflowing_sub : FuncData where
  inputTypes := [RangeCheck, U8, U8]
  branches := [{ outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(UInt8)) _ (ρ : Q(UInt8)) => 
                   q(($a).val ≥ ($b).val ∧ $ρ = $a - $b) },
               -- TODO check branch order
               { outputTypes := [RangeCheck, U8]
                 condition := fun _ (a b : Q(UInt8)) _ (ρ : Q(UInt8)) =>
                   q(($a).val < ($b).val ∧ $ρ = $a - $b) }]

def u8_const (n : Q(UInt8)) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [U8]
                 condition := fun (ρ : Q(UInt8)) => q($ρ = $n) }]

def u8_eq : FuncData where
  inputTypes := [U8, U8]
  -- TODO double check the order of branches
  branches := [{ condition := fun (a b : Q(UInt8)) => q($a ≠ $b) },
               { condition := fun (a b : Q(UInt8)) => q($a = $b) }]

def uint8Libfuncs : Identifier → Option FuncData
| .name "u8_overflowing_add" [] .none      => u8_overflowing_add
| .name "u8_overflowing_sub" [] .none      => u8_overflowing_sub
| .name "u8_const" [.const n] .none        => u8_const q($n)
| .name "u8_eq" [] .none                   => u8_eq
| _ => .none
