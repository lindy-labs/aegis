import SierraLean.FuncDataUtil
import Mathlib.Data.ZMod.Basic

open Qq Sierra.SierraType

namespace Sierra

def U256_MOD :=
  115792089237316195423570985008687907853269984665640564039457584007913129639936

abbrev UInt256 := ZMod U256_MOD

namespace FuncData

def u256_is_zero : FuncData where
  inputTypes := [.Struct [.U128, .U128]]
  branches := [{ outputTypes := []
                 condition := fun (a : Q(UInt128 × UInt128)) => q($a = (0, 0)) },
               { outputTypes := [.NonZero <| .Struct [.U128, .U128]]
                 condition := fun (a ρ : Q(UInt128 × UInt128)) => q(($(a).1 ≠ 0 ∨ $(a).2 ≠ 0) ∧ $ρ = $a) }]

def uint256Libfuncs : Identifier → Option FuncData
| .name "u256_is_zero" [] .none => u256_is_zero
| _ => .none
