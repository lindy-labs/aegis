import SierraLean.FuncDataUtil
import Mathlib.Data.ZMod.Basic

open Qq Sierra.SierraType

namespace Sierra.FuncData

def u8_const (n : Q(Int)) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [U8]
                 condition := fun (ρ : Q(UInt8)) => q($ρ = ($n : F)) }]

def uint8Libfuncs : Identifier → Option FuncData
| .name "u8_const" [.const n] .none        => u8_const q($n)
| _ => .none
