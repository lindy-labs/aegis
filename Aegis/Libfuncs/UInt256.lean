import Aegis.Types
import Mathlib.Data.ZMod.Basic

open Qq Sierra.SierraType

namespace Sierra.FuncData

def u256_is_zero : FuncData where
  inputTypes := [.Struct [.U128, .U128]]
  branches := [{ outputTypes := []
                 condition := fun (a : Q(UInt128 × UInt128)) => q($a = (0, 0)) },
               { outputTypes := [.NonZero <| .Struct [.U128, .U128]]
                 condition := fun (a ρ : Q(UInt128 × UInt128)) =>
                   q($(a).2 ++ $(a).1 ≠ 0 ∧ $ρ = $a) }]

def u256_safe_divmod : FuncData where
  inputTypes := [.RangeCheck, .Struct [.U128, .U128], .Struct [.U128, .U128]]
  branches := [{ outputTypes := [.RangeCheck, .Struct [.U128, .U128], .Struct [.U128, .U128], .U128MulGuarantee]
                 condition := fun _ (a b : Q(UInt128 × UInt128))
                   _ (div mod : Q(UInt128 × UInt128)) _ =>
                   q($(div).2 ++ $(div).1 = ($(a).2 ++ $(a).1) / ($(b).2 ++ $(b).1)
                     ∧ $(mod).2 ++ $(mod).1 = ($(a).2 ++ $(a).1) % ($(b).2 ++ $(b).1)) }]

def u256_sqrt : FuncData where
  inputTypes := [.RangeCheck, .Struct [.U128, .U128]]
  branches := [{ outputTypes := [.RangeCheck, .U128]
                 condition := fun _ (a : Q(UInt128 × UInt128)) _ (ρ : Q(UInt128)) =>
                   q($ρ = ($(a).2 ++ $(a).1).toNat.sqrt) }]

def uint256Libfuncs : Identifier → Option FuncData
| .name "u256_is_zero" [] .none => u256_is_zero
| .name "u256_safe_divmod" [] .none => u256_safe_divmod
| .name "u256_sqrt" [] .none => u256_sqrt
| _ => .none
