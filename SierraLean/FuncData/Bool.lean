import SierraLean.FuncDataUtil
import Mathlib.Data.Bool.Basic
import Mathlib.Data.ZMod.Basic

open Qq

namespace Sierra.FuncData

def bool_xor_impl : FuncData where
  inputTypes := [q(Bool), q(Bool)]
  branches := [{ outputTypes := [q(Bool)], condition := fun a b ρ => q($ρ = xor $a $b) }]

def bool_or_impl : FuncData where
  inputTypes := [q(Bool), q(Bool)]
  branches := [{ outputTypes := [q(Bool)], condition := fun a b ρ => q($ρ = $a || $b) }]

def bool_and_impl : FuncData where
  inputTypes := [q(Bool), q(Bool)]
  branches := [{ outputTypes := [q(Bool)], condition := fun a b ρ => q($ρ = $a && $b) }]

def bool_not_impl : FuncData where
  inputTypes := [q(Bool)]
  branches := [{ outputTypes := [q(Bool)], condition := fun a ρ => q($ρ = !$a) }]
