import SierraLean.FuncDataUtil
import Mathlib.Data.ZMod.Basic

open Qq

namespace Sierra

def PRIME := 3618502788666131213697322783095070105623107215331596699973092056135872020481

abbrev F := ZMod PRIME

namespace FuncData

def felt252_const (n : Q(Int)) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [q(F)], condition := fun a => q($a = ($n : F)) }]

def felt252_add : FuncData where
  inputTypes := [q(F), q(F)]
  branches := [{ outputTypes := [q(F)], condition := fun a b ρ => q($ρ = $a + $b) }]

def felt252_sub : FuncData where
  inputTypes := [q(F), q(F)]
  branches := [{ outputTypes := [q(F)], condition := fun a b ρ => q($ρ = $a - $b) }]

def felt252_mul : FuncData where
  inputTypes := [q(F), q(F)]
  branches := [{ outputTypes := [q(F)], condition := fun a b ρ => q($ρ = $a * $b) }]

def felt252_is_zero : FuncData where
  inputTypes := [q(F)]
  branches := [{ outputTypes := [],
                 condition := fun a => q($a = 0) },
               { outputTypes := [q(F)], -- TODO Actually the condition is baked into the output type here
                 condition := fun a _ => q($a ≠ 0) }]

def felt252Libfuncs : Identifier → Option FuncData
| .name "felt252_const" [.const n] => FuncData.felt252_const q($n)
| .name "felt252_add" []           => FuncData.felt252_add
| .name "felt252_sub" []           => FuncData.felt252_sub
| .name "felt252_mul" []           => FuncData.felt252_mul
| .name "felt252_is_zero" []       => FuncData.felt252_is_zero
| _                                => .none
