import Aegis.Types
import Mathlib.Data.ZMod.Basic

open Qq Lean

namespace Sierra.FuncData

variable (metadataRef : FVarId)

def pedersen : FuncData where
  inputTypes := [.Pedersen, .Felt252, .Felt252]
  branches := [{ outputTypes := [.Pedersen, .Felt252]
                 condition := fun _ (a b : Q(F)) _ (ρ : Q(F)) =>
                   let m : Q(Metadata) := .fvar metadataRef
                   q($ρ = $(m).pedersen $a $b) }]

def hashLibfuncs : Identifier → Option FuncData
| .name "pedersen" [] .none => pedersen metadataRef
| _                         => .none
