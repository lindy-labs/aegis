import Aegis.FuncDataUtil

open Qq Lean Sierra

namespace Sierra.FuncData

def null (t : SierraType) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [.Nullable t]
                 condition := fun (ρ : Q(Option $(⟦t⟧))) => q($ρ = .none) }]

def nullable_from_box (t : SierraType) : FuncData where
  inputTypes := [.Box t]
  branches := [{ outputTypes := [.Nullable t]
                 condition := fun (a : Q($(⟦t⟧))) (ρ : Q(Option $(⟦t⟧))) => q($ρ = .some $a) }]

def match_nullable (t : SierraType) : FuncData where
  inputTypes := [.Nullable t]
  branches := [{ outputTypes := []
                 condition := fun (a : Q(Option $(⟦t⟧))) => q($a = .none) },
               { outputTypes := [.Box t]
                 condition := fun (a : Q(Option $(⟦t⟧))) (ρ : Q($(⟦t⟧))) => q($a = .some $ρ) }]

def nullableLibfuncs (typeRefs : HashMap Identifier SierraType) : Identifier → Option FuncData
| .name "null" [.identifier ident] .none => return null (← typeRefs.find? ident)
| .name "nullable_from_box" [.identifier ident] .none =>
  return nullable_from_box (← typeRefs.find? ident)
| .name "match_nullable" [.identifier ident] .none =>
  return match_nullable (← typeRefs.find? ident)
| _ => .none
