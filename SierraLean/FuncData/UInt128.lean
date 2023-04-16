import SierraLean.FuncDataUtil
import Mathlib.Data.ZMod.Basic

open Qq

namespace Sierra

abbrev UInt128 := ZMod <| 2^128

namespace FuncData

def u128_overflowing_add : FuncData where
  inputTypes := [q(UInt128), q(UInt128)]
  branches := [{ outputTypes := [q(UInt128)], condition := fun a b ρ => q($ρ = $a + $b) }]

def u128_overflowing_sub : FuncData where
  inputTypes := [q(UInt128), q(UInt128)]
  branches := [{ outputTypes := [q(UInt128)], condition := fun a b ρ => q($ρ = $a - $b) }]
