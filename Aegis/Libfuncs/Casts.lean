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
| _ => .none
