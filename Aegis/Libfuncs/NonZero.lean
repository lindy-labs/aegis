import Aegis.Types

open Qq Lean Sierra

namespace Sierra.FuncData

def unwrap_non_zero (t : SierraType) : FuncData where
  inputTypes := [.NonZero t]
  branches := [{ outputTypes := [t]
                 condition := fun (a ρ : Q($(⟦t⟧))) => q($ρ = $a) }]

def nonZeroLibfuncs (typeRefs : Std.HashMap Identifier SierraType) : Identifier → Option FuncData
| .name "unwrap_non_zero" [.identifier ident] .none =>
  return unwrap_non_zero (← typeRefs[ident]?)
| _ => .none
