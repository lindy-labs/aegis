import Aegis.Types

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
                   q($ρ = $(a).cast) }]

def u8u32_upcast : FuncData where
  inputTypes := [.U8]
  branches := [{ outputTypes := [.U32]
                 condition := fun (a : Q(UInt8)) (ρ : Q(UInt32)) =>
                   q($ρ = $(a).cast) }]

def u8u64_upcast : FuncData where
  inputTypes := [.U8]
  branches := [{ outputTypes := [.U64]
                 condition := fun (a : Q(UInt8)) (ρ : Q(UInt64)) =>
                   q($ρ = $(a).cast) }]

def u16u16_upcast : FuncData where
  inputTypes := [.U16]
  branches := [{ outputTypes := [.U16]
                 condition := fun (a ρ : Q(UInt16)) =>
                   q($ρ = $a) }]

def u8u128_upcast : FuncData where
  inputTypes := [.U8]
  branches := [{ outputTypes := [.U128]
                 condition := fun (a : Q(UInt8)) (ρ : Q(UInt128)) =>
                   q($ρ = $(a).cast) }]

def u16u32_upcast : FuncData where
  inputTypes := [.U16]
  branches := [{ outputTypes := [.U32]
                 condition := fun (a : Q(UInt16)) (ρ : Q(UInt32)) =>
                   q($ρ = $(a).cast) }]

def u16u64_upcast : FuncData where
  inputTypes := [.U16]
  branches := [{ outputTypes := [.U64]
                 condition := fun (a : Q(UInt16)) (ρ : Q(UInt64)) =>
                   q($ρ = $(a).cast) }]

def u16u128_upcast : FuncData where
  inputTypes := [.U16]
  branches := [{ outputTypes := [.U128]
                 condition := fun (a : Q(UInt16)) (ρ : Q(UInt128)) =>
                   q($ρ = $(a).cast) }]

def u32u32_upcast : FuncData where
  inputTypes := [.U32]
  branches := [{ outputTypes := [.U32]
                 condition := fun (a ρ : Q(UInt32)) =>
                   q($ρ = $a) }]

def u32u64_upcast : FuncData where
  inputTypes := [.U32]
  branches := [{ outputTypes := [.U64]
                 condition := fun (a : Q(UInt32)) (ρ : Q(UInt64)) =>
                   q($ρ = $(a).cast) }]

def u32u128_upcast : FuncData where
  inputTypes := [.U32]
  branches := [{ outputTypes := [.U128]
                 condition := fun (a : Q(UInt32)) (ρ : Q(UInt128)) =>
                   q($ρ = $(a).cast) }]

def u64u64_upcast : FuncData where
  inputTypes := [.U64]
  branches := [{ outputTypes := [.U64]
                 condition := fun (a ρ : Q(UInt64)) =>
                   q($ρ = $a) }]

def u64u128_upcast : FuncData where
  inputTypes := [.U64]
  branches := [{ outputTypes := [.U128]
                 condition := fun (a : Q(UInt64)) (ρ : Q(UInt128)) =>
                   q($ρ = $(a).cast) }]

def u128u128_upcast : FuncData where
  inputTypes := [.U128]
  branches := [{ outputTypes := [.U128]
                 condition := fun (a ρ : Q(UInt128)) =>
                   q($ρ = $a) }]

def u16u8_downcast : FuncData where
  inputTypes := [.RangeCheck, .U16]
  branches := [{ outputTypes := [.RangeCheck, .U8]
                 condition := fun _ (a : Q(UInt16)) _ (ρ : Q(UInt8)) =>
                   q($(a).val < U8_MOD ∧ $ρ = $(a).cast) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt16)) _ =>
                   q(U8_MOD ≤ $(a).val)}]

def u32u8_downcast : FuncData where
  inputTypes := [.RangeCheck, .U32]
  branches := [{ outputTypes := [.RangeCheck, .U8]
                 condition := fun _ (a : Q(UInt32)) _ (ρ : Q(UInt8)) =>
                   q($(a).val < U8_MOD ∧ $ρ = $(a).cast) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt32)) _ =>
                   q(U8_MOD ≤ $(a).val)}]

def u32u16_downcast : FuncData where
  inputTypes := [.RangeCheck, .U32]
  branches := [{ outputTypes := [.RangeCheck, .U16]
                 condition := fun _ (a : Q(UInt32)) _ (ρ : Q(UInt16)) =>
                   q($(a).val < U16_MOD ∧ $ρ = $(a).cast) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt32)) _ =>
                   q(U16_MOD ≤ $(a).val)}]

def u64u8_downcast : FuncData where
  inputTypes := [.RangeCheck, .U64]
  branches := [{ outputTypes := [.RangeCheck, .U8]
                 condition := fun _ (a : Q(UInt64)) _ (ρ : Q(UInt8)) =>
                   q($(a).val < U8_MOD ∧ $ρ = $(a).cast) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt64)) _ =>
                   q(U8_MOD ≤ $(a).val)}]

def u64u16_downcast : FuncData where
  inputTypes := [.RangeCheck, .U64]
  branches := [{ outputTypes := [.RangeCheck, .U16]
                 condition := fun _ (a : Q(UInt64)) _ (ρ : Q(UInt16)) =>
                   q($(a).val < U16_MOD ∧ $ρ = $(a).cast) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt64)) _ =>
                   q(U16_MOD ≤ $(a).val)}]

def u64u32_downcast : FuncData where
  inputTypes := [.RangeCheck, .U64]
  branches := [{ outputTypes := [.RangeCheck, .U32]
                 condition := fun _ (a : Q(UInt64)) _ (ρ : Q(UInt32)) =>
                   q($(a).val < U32_MOD ∧ $ρ = $(a).cast) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt64)) _ =>
                   q(U32_MOD ≤ $(a).val)}]

def u128u8_downcast : FuncData where
  inputTypes := [.RangeCheck, .U128]
  branches := [{ outputTypes := [.RangeCheck, .U8]
                 condition := fun _ (a : Q(UInt128)) _ (ρ : Q(UInt8)) =>
                   q($(a).val < U8_MOD ∧ $ρ = $(a).cast) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt128)) _ =>
                   q(U8_MOD ≤ $(a).val)}]

def u128u16_downcast : FuncData where
  inputTypes := [.RangeCheck, .U128]
  branches := [{ outputTypes := [.RangeCheck, .U16]
                 condition := fun _ (a : Q(UInt128)) _ (ρ : Q(UInt16)) =>
                   q($(a).val < U16_MOD ∧ $ρ = $(a).cast) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt128)) _ =>
                   q(U16_MOD ≤ $(a).val)}]

def u128u32_downcast : FuncData where
  inputTypes := [.RangeCheck, .U128]
  branches := [{ outputTypes := [.RangeCheck, .U32]
                 condition := fun _ (a : Q(UInt128)) _ (ρ : Q(UInt32)) =>
                   q($(a).val < U32_MOD ∧ $ρ = $(a).cast) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt128)) _ =>
                   q(U32_MOD ≤ $(a).val)}]

def u128u64_downcast : FuncData where
  inputTypes := [.RangeCheck, .U128]
  branches := [{ outputTypes := [.RangeCheck, .U64]
                 condition := fun _ (a : Q(UInt128)) _ (ρ : Q(UInt64)) =>
                   q($(a).val < U64_MOD ∧ $ρ = $(a).cast) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(UInt128)) _ =>
                   q(U64_MOD ≤ $(a).val)}]

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
| _ => .none
