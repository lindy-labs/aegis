import SierraLean.FuncDataUtil
import Mathlib.Data.ZMod.Basic

open Qq Sierra.SierraType

namespace Sierra

namespace FuncData

def pedersen : FuncData where
  inputTypes := [Pedersen, Felt252, Felt252]
  branches := [{ outputTypes := [Pedersen, Felt252]
                 condition := fun _ _ _ _ _ => q(True) }] --TODO

def hashLibfuncs : Identifier → Option FuncData
| .name "pedersen" [] .none => pedersen
| _                         => .none
