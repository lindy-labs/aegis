import SierraLean.FuncDataUtil
import Mathlib.Data.ZMod.Basic

open Qq Sierra.SierraType

namespace Sierra.FuncData

def contract_address_try_from_felt252 : FuncData where
  inputTypes := [.RangeCheck, .Felt252]
  branches := [{ outputTypes := [.RangeCheck, .ContractAddress]
                 condition := fun _ (a : Q(F)) _ (ρ : Q(ContractAddress)) =>
                   q(CONTRACT_ADDRESS_MOD < $(a).val ∧ $ρ = $(a).cast) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(F)) _ => q($(a).val ≤ CONTRACT_ADDRESS_MOD) }]

def contractAddressLibfuncs : Identifier → Option FuncData
| .name "contract_address_try_from_felt252" [] .none => contract_address_try_from_felt252
| _ => .none