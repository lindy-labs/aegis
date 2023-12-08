import Aegis.Types
import Mathlib.Data.ZMod.Basic

open Qq Sierra.SierraType

namespace Sierra.FuncData

def u256_is_zero : FuncData where
  inputTypes := [.Struct [.U128, .U128]]
  branches := [{ outputTypes := []
                 condition := fun (a : Q(UInt128 × UInt128)) => q($a = (0, 0)) },
               { outputTypes := [.NonZero <| .Struct [.U128, .U128]]
                 condition := fun (a ρ : Q(UInt128 × UInt128)) => q(($(a).1 ≠ 0 ∨ $(a).2 ≠ 0) ∧ $ρ = $a) }]

def u256_safe_divmod : FuncData where
  inputTypes := [.RangeCheck, .Struct [.U128, .U128], .Struct [.U128, .U128]]
  branches := [{ outputTypes := [.RangeCheck, .Struct [.U128, .U128], .Struct [.U128, .U128], .U128MulGuarantee]
                 condition := fun _ (a b : Q(UInt128 × UInt128))
                   _ (div mod : Q(UInt128 × UInt128)) _ =>
                   -- TODO maybe replace by a direct characterization in the future
                   q(U128_MOD * $(div).2.val + $(div).1.val =
                       (U128_MOD * $(a).2.val + $(a).1.val) / (U128_MOD * $(b).2.val + $(b).1.val)
                     ∧ U128_MOD * $(mod).2.val + $(mod).1.val =
                       (U128_MOD * $(a).2.val + $(a).1.val) % (U128_MOD * $(b).2.val + $(b).1.val)) }]

def uint256Libfuncs : Identifier → Option FuncData
| .name "u256_is_zero" [] .none => u256_is_zero
| .name "u256_safe_divmod" [] .none => u256_safe_divmod
| _ => .none
