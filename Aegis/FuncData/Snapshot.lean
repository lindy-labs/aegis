import Aegis.FuncDataUtil

open Qq Lean Sierra

namespace Sierra.FuncData

def snapshot_take (t : SierraType) : FuncData where
  inputTypes := [t]
  branches := [{ outputTypes := [t, .Snapshot t]
                 condition := fun a ρ₁ (ρ₂ : Q($(⟦t⟧))) => q($ρ₁ = $a ∧ $ρ₂ = $a) }]

def snapshotLibfuncs (typeRefs : HashMap Identifier SierraType) : Identifier → Option FuncData
| .name "snapshot_take" [.identifier ident] _ => return snapshot_take (← typeRefs.find? ident)
| _ => .none
