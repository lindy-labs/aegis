import Aegis.Types

open Qq Lean Sierra

namespace Sierra.FuncData

def storage_base_address_from_felt252 : FuncData where
  inputTypes := [.RangeCheck, .Felt252]
  branches := [{ outputTypes := [.RangeCheck, .StorageBaseAddress]
                 condition := fun _ (a : Q(F)) _ (ρ : Q(StorageBaseAddress)) =>
                   q($ρ = $(a).cast) }]

def storage_address_from_base_and_offset : FuncData where
  inputTypes := [.StorageBaseAddress, .U8]
  branches := [{ outputTypes := [.StorageAddress]
                 condition := fun
                   -- TODO Why can't I use the abbreviateion (see `quote4` issue #13)
                   (a : Q(ZMod 3618502788666131106986593281521497120414687020801267626233049500247285300992))
                   (b : Q(UInt8))
                   (ρ : Q(ZMod 3618502788666131106986593281521497120414687020801267626233049500247285301248)) =>
                     q($ρ = $(a).cast + $(b).cast) }]

def storage_address_try_from_felt252 : FuncData where
  inputTypes := [.Felt252]
  branches := [{ outputTypes := [.RangeCheck, .StorageAddress]
                 condition := fun (a : Q(F)) _ (ρ : Q(StorageAddress)) =>
                   q($(a).val < ADDRESS_MOD ∧ $ρ = $(a).cast) },
               { outputTypes := [.RangeCheck] }]

def storage_address_from_base : FuncData where
  inputTypes := [.StorageBaseAddress]
  branches := [{ outputTypes := [.StorageAddress]
                 condition := fun (a : Q(ZMod 3618502788666131106986593281521497120414687020801267626233049500247285300992))
                   (ρ : Q(ZMod 3618502788666131106986593281521497120414687020801267626233049500247285301248)) =>
                     q($ρ = $(a).cast) }]

def storage_base_address_const (n : Q(StorageBaseAddress)) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [.StorageBaseAddress]
                 condition := fun (ρ : Q(StorageBaseAddress)) => q($ρ = $n) }]

def storageLibfuncs : Identifier → Option FuncData
| .name "storage_base_address_from_felt252" [] .none => storage_base_address_from_felt252
| .name "storage_address_from_base_and_offset" [] .none => storage_address_from_base_and_offset
| .name "storage_address_try_from_felt252" [] .none => storage_address_try_from_felt252
| .name "storage_address_from_base" [] .none => storage_address_from_base
| .name "storage_base_address_const" [.const n] .none => storage_base_address_const q($n)
| _ => .none
