import Aegis.Types
import Mathlib.Data.ZMod.ValMinAbs

open Qq Sierra.SierraType

namespace Sierra.FuncData

def u8u8_upcast : FuncData where
  inputTypes := [.U8]
  branches := [{ outputTypes := [.U8]
                 condition := fun (a ρ : Q(UInt8)) =>
                   q($ρ = $a) }]

def u8u16_upcast : FuncData where
  inputTypes := [.U8]
  branches := [{ outputTypes := [.U16]
                 condition := fun (a : Q(UInt8)) (ρ : Q(UInt16)) =>
                   q($ρ = $(a).zeroExtend _) }]

def u8u32_upcast : FuncData where
  inputTypes := [.U8]
  branches := [{ outputTypes := [.U32]
                 condition := fun (a : Q(UInt8)) (ρ : Q(UInt32)) =>
                   q($ρ = $(a).zeroExtend _) }]

def u8u64_upcast : FuncData where
  inputTypes := [.U8]
  branches := [{ outputTypes := [.U64]
                 condition := fun (a : Q(UInt8)) (ρ : Q(UInt64)) =>
                   q($ρ = $(a).zeroExtend _) }]

def u16u16_upcast : FuncData where
  inputTypes := [.U16]
  branches := [{ outputTypes := [.U16]
                 condition := fun (a ρ : Q(UInt16)) =>
                   q($ρ = $a) }]

def u8u128_upcast : FuncData where
  inputTypes := [.U8]
  branches := [{ outputTypes := [.U128]
                 condition := fun (a : Q(UInt8)) (ρ : Q(UInt128)) =>
                   q($ρ = $(a).zeroExtend _) }]

def u16u32_upcast : FuncData where
  inputTypes := [.U16]
  branches := [{ outputTypes := [.U32]
                 condition := fun (a : Q(UInt16)) (ρ : Q(UInt32)) =>
                   q($ρ = $(a).zeroExtend _) }]

def u16u64_upcast : FuncData where
  inputTypes := [.U16]
  branches := [{ outputTypes := [.U64]
                 condition := fun (a : Q(UInt16)) (ρ : Q(UInt64)) =>
                   q($ρ = $(a).zeroExtend _) }]

def u16u128_upcast : FuncData where
  inputTypes := [.U16]
  branches := [{ outputTypes := [.U128]
                 condition := fun (a : Q(UInt16)) (ρ : Q(UInt128)) =>
                   q($ρ = $(a).zeroExtend _) }]

def u32u32_upcast : FuncData where
  inputTypes := [.U32]
  branches := [{ outputTypes := [.U32]
                 condition := fun (a ρ : Q(UInt32)) =>
                   q($ρ = $a) }]

def u32u64_upcast : FuncData where
  inputTypes := [.U32]
  branches := [{ outputTypes := [.U64]
                 condition := fun (a : Q(UInt32)) (ρ : Q(UInt64)) =>
                   q($ρ = $(a).zeroExtend _) }]

def u32u128_upcast : FuncData where
  inputTypes := [.U32]
  branches := [{ outputTypes := [.U128]
                 condition := fun (a : Q(UInt32)) (ρ : Q(UInt128)) =>
                   q($ρ = $(a).zeroExtend _) }]

def u64u64_upcast : FuncData where
  inputTypes := [.U64]
  branches := [{ outputTypes := [.U64]
                 condition := fun (a ρ : Q(UInt64)) =>
                   q($ρ = $a) }]

def u64u128_upcast : FuncData where
  inputTypes := [.U64]
  branches := [{ outputTypes := [.U128]
                 condition := fun (a : Q(UInt64)) (ρ : Q(UInt128)) =>
                   q($ρ = $(a).zeroExtend _) }]

def u128u128_upcast : FuncData where
  inputTypes := [.U128]
  branches := [{ outputTypes := [.U128]
                 condition := fun (a ρ : Q(UInt128)) =>
                   q($ρ = $a) }]

def u16u8_downcast : FuncData where
  inputTypes := [.RangeCheck, .U16]
  branches := [{ outputTypes := [.RangeCheck, .U8]
                 condition := fun _ (a : Q(UInt16)) _ (ρ : Q(UInt8)) =>
                   q($(a).toNat < U8_MOD ∧ $ρ = $(a).zeroExtend _) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt16)) _ => q(U8_MOD ≤ $(a).toNat)}]

def u32u8_downcast : FuncData where
  inputTypes := [.RangeCheck, .U32]
  branches := [{ outputTypes := [.RangeCheck, .U8]
                 condition := fun _ (a : Q(UInt32)) _ (ρ : Q(UInt8)) =>
                   q($(a).toNat < U8_MOD ∧ $ρ = $(a).zeroExtend _) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt32)) _ =>
                   q(U8_MOD ≤ $(a).toNat)}]

def u32u16_downcast : FuncData where
  inputTypes := [.RangeCheck, .U32]
  branches := [{ outputTypes := [.RangeCheck, .U16]
                 condition := fun _ (a : Q(UInt32)) _ (ρ : Q(UInt16)) =>
                   q($(a).toNat < U16_MOD ∧ $ρ = $(a).zeroExtend _) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt32)) _ =>
                   q(U16_MOD ≤ $(a).toNat)}]

def u64u8_downcast : FuncData where
  inputTypes := [.RangeCheck, .U64]
  branches := [{ outputTypes := [.RangeCheck, .U8]
                 condition := fun _ (a : Q(UInt64)) _ (ρ : Q(UInt8)) =>
                   q($(a).toNat < U8_MOD ∧ $ρ = $(a).zeroExtend _) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt64)) _ =>
                   q(U8_MOD ≤ $(a).toNat)}]

def u64u16_downcast : FuncData where
  inputTypes := [.RangeCheck, .U64]
  branches := [{ outputTypes := [.RangeCheck, .U16]
                 condition := fun _ (a : Q(UInt64)) _ (ρ : Q(UInt16)) =>
                   q($(a).toNat < U16_MOD ∧ $ρ = $(a).zeroExtend _) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt64)) _ =>
                   q(U16_MOD ≤ $(a).toNat)}]

def u64u32_downcast : FuncData where
  inputTypes := [.RangeCheck, .U64]
  branches := [{ outputTypes := [.RangeCheck, .U32]
                 condition := fun _ (a : Q(UInt64)) _ (ρ : Q(UInt32)) =>
                   q($(a).toNat < U32_MOD ∧ $ρ = $(a).zeroExtend _) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt64)) _ =>
                   q(U32_MOD ≤ $(a).toNat)}]

def u128u8_downcast : FuncData where
  inputTypes := [.RangeCheck, .U128]
  branches := [{ outputTypes := [.RangeCheck, .U8]
                 condition := fun _ (a : Q(UInt128)) _ (ρ : Q(UInt8)) =>
                   q($(a).toNat < U8_MOD ∧ $ρ = $(a).zeroExtend _) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt128)) _ =>
                   q(U8_MOD ≤ $(a).toNat)}]

def u128u16_downcast : FuncData where
  inputTypes := [.RangeCheck, .U128]
  branches := [{ outputTypes := [.RangeCheck, .U16]
                 condition := fun _ (a : Q(UInt128)) _ (ρ : Q(UInt16)) =>
                   q($(a).toNat < U16_MOD ∧ $ρ = $(a).zeroExtend _) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt128)) _ =>
                   q(U16_MOD ≤ $(a).toNat)}]

def u128u32_downcast : FuncData where
  inputTypes := [.RangeCheck, .U128]
  branches := [{ outputTypes := [.RangeCheck, .U32]
                 condition := fun _ (a : Q(UInt128)) _ (ρ : Q(UInt32)) =>
                   q($(a).toNat < U32_MOD ∧ $ρ = $(a).zeroExtend _) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt128)) _ =>
                   q(U32_MOD ≤ $(a).toNat)}]

def u128u64_downcast : FuncData where
  inputTypes := [.RangeCheck, .U128]
  branches := [{ outputTypes := [.RangeCheck, .U64]
                 condition := fun _ (a : Q(UInt128)) _ (ρ : Q(UInt64)) =>
                   q($(a).toNat < U64_MOD ∧ $ρ = $(a).zeroExtend _) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt128)) _ =>
                   q(U64_MOD ≤ $(a).toNat)}]

def BoundedIntu8_upcast (min max : ℤ) : FuncData where
  inputTypes := [BoundedInt min max]
  branches := [{ outputTypes := [U8]
                 condition := fun (a : Q(Int)) (ρ : Q(UInt8)) => q($ρ = $a) }]

def BoundedIntu16_upcast (min max : ℤ) : FuncData where
  inputTypes := [BoundedInt min max]
  branches := [{ outputTypes := [U16]
                 condition := fun (a : Q(Int)) (ρ : Q(UInt16)) => q($ρ = $a) }]

def BoundedIntu32_upcast (min max : ℤ) : FuncData where
  inputTypes := [BoundedInt min max]
  branches := [{ outputTypes := [U32]
                 condition := fun (a : Q(Int)) (ρ : Q(UInt32)) => q($ρ = $a) }]

def BoundedIntu64_upcast (min max : ℤ) : FuncData where
  inputTypes := [BoundedInt min max]
  branches := [{ outputTypes := [U64]
                 condition := fun (a : Q(Int)) (ρ : Q(UInt64)) => q($ρ = $a) }]

def BoundedIntu128_upcast (min max : ℤ) : FuncData where
  inputTypes := [BoundedInt min max]
  branches := [{ outputTypes := [U128]
                 condition := fun (a : Q(Int)) (ρ : Q(UInt128)) => q($ρ = $a) }]

def BoundedInti8_upcast (min max : ℤ) : FuncData where
  inputTypes := [BoundedInt min max]
  branches := [{ outputTypes := [I8]
                 condition := fun (a : Q(Int)) (ρ : Q(Int8)) => q($ρ = $a) }]

def BoundedInti16_upcast (min max : ℤ) : FuncData where
  inputTypes := [BoundedInt min max]
  branches := [{ outputTypes := [I16]
                 condition := fun (a : Q(Int)) (ρ : Q(Int16)) => q($ρ = $a) }]

def BoundedInti32_upcast (min max : ℤ) : FuncData where
  inputTypes := [BoundedInt min max]
  branches := [{ outputTypes := [I32]
                 condition := fun (a : Q(Int)) (ρ : Q(Int32)) => q($ρ = $a) }]

def BoundedInti64_upcast (min max : ℤ) : FuncData where
  inputTypes := [BoundedInt min max]
  branches := [{ outputTypes := [I64]
                 condition := fun (a : Q(Int)) (ρ : Q(Int64)) => q($ρ = $a) }]

def BoundedInti128_upcast (min max : ℤ) : FuncData where
  inputTypes := [BoundedInt min max]
  branches := [{ outputTypes := [I128]
                 condition := fun (a : Q(Int)) (ρ : Q(UInt128)) => q($ρ = $a) }]

def u8BoundedInt_downcast (min max : ℤ) : FuncData where
  inputTypes := [.RangeCheck, .U8]
  branches := [{ outputTypes := [.RangeCheck, .BoundedInt min max]
                 condition := fun _ (a : Q(UInt8)) _ (ρ : Q(Int)) =>
                   q($min ≤ $(a).toNat ∧ $(a).toNat ≤ $max ∧ $ρ = $(a).toNat) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt8)) _ =>
                   q($(a).toNat < $min ∨ $max < $(a).toNat)}]

def u16BoundedInt_downcast (min max : ℤ) : FuncData where
  inputTypes := [.RangeCheck, .U16]
  branches := [{ outputTypes := [.RangeCheck, .BoundedInt min max]
                 condition := fun _ (a : Q(UInt16)) _ (ρ : Q(Int)) =>
                   q($min ≤ $(a).toNat ∧ $(a).toNat ≤ $max ∧ $ρ = $(a).toNat) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt16)) _ =>
                   q($(a).toNat < $min ∨ $max < $(a).toNat)}]

def u32BoundedInt_downcast (min max : ℤ) : FuncData where
  inputTypes := [.RangeCheck, .U32]
  branches := [{ outputTypes := [.RangeCheck, .BoundedInt min max]
                 condition := fun _ (a : Q(UInt32)) _ (ρ : Q(Int)) =>
                   q($min ≤ $(a).toNat ∧ $(a).toNat ≤ $max ∧ $ρ = $(a).toNat) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt32)) _ =>
                   q($(a).toNat < $min ∨ $max < $(a).toNat)}]

def u64BoundedInt_downcast (min max : ℤ) : FuncData where
  inputTypes := [.RangeCheck, .U64]
  branches := [{ outputTypes := [.RangeCheck, .BoundedInt min max]
                 condition := fun _ (a : Q(UInt64)) _ (ρ : Q(Int)) =>
                   q($min ≤ $(a).toNat ∧ $(a).toNat ≤ $max ∧ $ρ = $(a).toNat) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt64)) _ =>
                   q($(a).toNat < $min ∨ $max < $(a).toNat)}]

def u128BoundedInt_downcast (min max : ℤ) : FuncData where
  inputTypes := [.RangeCheck, .U128]
  branches := [{ outputTypes := [.RangeCheck, .BoundedInt min max]
                 condition := fun _ (a : Q(UInt128)) _ (ρ : Q(Int)) =>
                   q($min ≤ $(a).toNat ∧ $(a).toNat ≤ $max ∧ $ρ = $(a).toNat) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt128)) _ =>
                   q($(a).toNat < $min ∨ $max < $(a).toNat)}]

def i8u8_downcast : FuncData where
  inputTypes := [.RangeCheck, .I8]
  branches := [{ outputTypes := [.RangeCheck, .U8]
                 condition := fun _ (a : Q(Int8)) _ (ρ : Q(UInt8)) =>
                   q(0 ≤ $(a).toInt ∧ $ρ = $(a).abs) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt8)) _ =>
                   q($(a).toInt < 0)}]

def i16u16_downcast : FuncData where
  inputTypes := [.RangeCheck, .I16]
  branches := [{ outputTypes := [.RangeCheck, .U16]
                 condition := fun _ (a : Q(Int16)) _ (ρ : Q(UInt16)) =>
                   q(0 ≤ $(a).toInt ∧ $ρ = $(a).abs) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt16)) _ =>
                   q($(a).toInt < 0)}]

def i32u32_downcast : FuncData where
  inputTypes := [.RangeCheck, .I32]
  branches := [{ outputTypes := [.RangeCheck, .U32]
                 condition := fun _ (a : Q(Int32)) _ (ρ : Q(UInt32)) =>
                   q(0 ≤ $(a).toInt ∧ $ρ = $(a).abs) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt32)) _ =>
                   q($(a).toInt < 0)}]

def i64u64_downcast : FuncData where
  inputTypes := [.RangeCheck, .I64]
  branches := [{ outputTypes := [.RangeCheck, .U64]
                 condition := fun _ (a : Q(Int64)) _ (ρ : Q(UInt64)) =>
                   q(0 ≤ $(a).toInt ∧ $ρ = $(a).abs) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt64)) _ =>
                   q($(a).toInt < 0)}]

def i128u128_downcast : FuncData where
  inputTypes := [.RangeCheck, .I128]
  branches := [{ outputTypes := [.RangeCheck, .U128]
                 condition := fun _ (a : Q(Int128)) _ (ρ : Q(UInt128)) =>
                   q(0 ≤ $(a).toInt ∧ $ρ = $(a).abs) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt128)) _ =>
                   q($(a).toInt < 0)}]

def castsLibfuncs : Identifier → Option FuncData
| .name "upcast" [.identifier (.name "u8" [] .none), .identifier (.name "u8" [] .none)] .none =>
  u8u8_upcast
| .name "upcast" [.identifier (.name "u8" [] .none), .identifier (.name "u16" [] .none)] .none =>
  u8u16_upcast
| .name "upcast" [.identifier (.name "u8" [] .none), .identifier (.name "u32" [] .none)] .none =>
  u8u32_upcast
| .name "upcast" [.identifier (.name "u8" [] .none), .identifier (.name "u64" [] .none)] .none =>
  u8u64_upcast
| .name "upcast" [.identifier (.name "u8" [] .none), .identifier (.name "u128" [] .none)] .none =>
  u8u128_upcast
| .name "upcast" [.identifier (.name "u16" [] .none), .identifier (.name "u16" [] .none)] .none =>
  u16u16_upcast
| .name "upcast" [.identifier (.name "u16" [] .none), .identifier (.name "u32" [] .none)] .none =>
  u16u32_upcast
| .name "upcast" [.identifier (.name "u16" [] .none), .identifier (.name "u64" [] .none)] .none =>
  u16u64_upcast
| .name "upcast" [.identifier (.name "u16" [] .none), .identifier (.name "u128" [] .none)] .none =>
  u16u128_upcast
| .name "upcast" [.identifier (.name "u32" [] .none), .identifier (.name "u32" [] .none)] .none =>
  u32u32_upcast
| .name "upcast" [.identifier (.name "u32" [] .none), .identifier (.name "u64" [] .none)] .none =>
  u32u64_upcast
| .name "upcast" [.identifier (.name "u32" [] .none), .identifier (.name "u128" [] .none)] .none =>
  u32u128_upcast
| .name "upcast" [.identifier (.name "u64" [] .none), .identifier (.name "u64" [] .none)] .none =>
  u64u64_upcast
| .name "upcast" [.identifier (.name "u64" [] .none), .identifier (.name "u128" [] .none)] .none =>
  u64u128_upcast
| .name "upcast" [.identifier (.name "u128" [] .none), .identifier (.name "u128" [] .none)] .none =>
  u128u128_upcast
| .name "upcast" [.identifier (.name "BoundedInt" [.const min, .const max] .none), .identifier (.name "u8" [] .none)] .none =>
  BoundedIntu8_upcast min max
| .name "upcast" [.identifier (.name "BoundedInt" [.const min, .const max] .none), .identifier (.name "u16" [] .none)] .none =>
  BoundedIntu16_upcast min max
| .name "upcast" [.identifier (.name "BoundedInt" [.const min, .const max] .none), .identifier (.name "u32" [] .none)] .none =>
  BoundedIntu32_upcast min max
| .name "upcast" [.identifier (.name "BoundedInt" [.const min, .const max] .none), .identifier (.name "u64" [] .none)] .none =>
  BoundedIntu64_upcast min max
| .name "upcast" [.identifier (.name "BoundedInt" [.const min, .const max] .none), .identifier (.name "u128" [] .none)] .none =>
  BoundedIntu128_upcast min max
| .name "upcast" [.identifier (.name "BoundedInt" [.const min, .const max] .none), .identifier (.name "i8" [] .none)] .none =>
  BoundedInti8_upcast min max
| .name "upcast" [.identifier (.name "BoundedInt" [.const min, .const max] .none), .identifier (.name "i16" [] .none)] .none =>
  BoundedInti16_upcast min max
| .name "upcast" [.identifier (.name "BoundedInt" [.const min, .const max] .none), .identifier (.name "i32" [] .none)] .none =>
  BoundedInti32_upcast min max
| .name "upcast" [.identifier (.name "BoundedInt" [.const min, .const max] .none), .identifier (.name "i64" [] .none)] .none =>
  BoundedInti64_upcast min max
| .name "upcast" [.identifier (.name "BoundedInt" [.const min, .const max] .none), .identifier (.name "i128" [] .none)] .none =>
  BoundedInti128_upcast min max
| .name "downcast" [.identifier (.name "u16" [] .none), .identifier (.name "u8" [] .none)] .none =>
  u16u8_downcast
| .name "downcast" [.identifier (.name "u32" [] .none), .identifier (.name "u8" [] .none)] .none =>
  u32u8_downcast
| .name "downcast" [.identifier (.name "u32" [] .none), .identifier (.name "u16" [] .none)] .none =>
  u32u16_downcast
| .name "downcast" [.identifier (.name "u64" [] .none), .identifier (.name "u8" [] .none)] .none =>
  u64u8_downcast
| .name "downcast" [.identifier (.name "u64" [] .none), .identifier (.name "u16" [] .none)] .none =>
  u64u16_downcast
| .name "downcast" [.identifier (.name "u64" [] .none), .identifier (.name "u32" [] .none)] .none =>
  u64u32_downcast
| .name "downcast" [.identifier (.name "u128" [] .none), .identifier (.name "u8" [] .none)] .none =>
  u128u8_downcast
| .name "downcast" [.identifier (.name "u128" [] .none), .identifier (.name "u16" [] .none)] .none =>
  u128u16_downcast
| .name "downcast" [.identifier (.name "u128" [] .none), .identifier (.name "u32" [] .none)] .none =>
  u128u32_downcast
| .name "downcast" [.identifier (.name "u128" [] .none), .identifier (.name "u64" [] .none)] .none =>
  u128u64_downcast
| .name "downcast" [.identifier (.name "i8" [] .none), .identifier (.name "u8" [] .none)] .none =>
  i8u8_downcast
| .name "downcast" [.identifier (.name "i16" [] .none), .identifier (.name "u16" [] .none)] .none =>
  i16u16_downcast
| .name "downcast" [.identifier (.name "i32" [] .none), .identifier (.name "u32" [] .none)] .none =>
  i32u32_downcast
| .name "downcast" [.identifier (.name "i64" [] .none), .identifier (.name "u64" [] .none)] .none =>
  i64u64_downcast
| .name "downcast" [.identifier (.name "i128" [] .none), .identifier (.name "u128" [] .none)] .none =>
  i128u128_downcast
| .name "downcast" [.identifier (.name "u8" [] .none), .identifier (.name "BoundedInt" [.const min, .const max] .none)] .none =>
  u8BoundedInt_downcast min max
| .name "downcast" [.identifier (.name "u16" [] .none), .identifier (.name "BoundedInt" [.const min, .const max] .none)] .none =>
  u16BoundedInt_downcast min max
| .name "downcast" [.identifier (.name "u32" [] .none), .identifier (.name "BoundedInt" [.const min, .const max] .none)] .none =>
  u32BoundedInt_downcast min max
| .name "downcast" [.identifier (.name "u64" [] .none), .identifier (.name "BoundedInt" [.const min, .const max] .none)] .none =>
  u64BoundedInt_downcast min max
| .name "downcast" [.identifier (.name "u128" [] .none), .identifier (.name "BoundedInt" [.const min, .const max] .none)] .none =>
  u128BoundedInt_downcast min max
| _ => .none
