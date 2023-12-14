import Aegis.Types

open Qq Lean Sierra

namespace Sierra.FuncData

variable (metadataRef : FVarId)

def null (t : SierraType) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [.Nullable t]
                 condition := fun (ρ : Q(Option $(⟦t⟧))) => q($ρ = .none) }]

def nullable_from_box (t : SierraType) : FuncData where
  inputTypes := [.Box t]
  branches := [{ outputTypes := [.Nullable t]
                 condition := fun (a : Q(Nat)) (ρ : Q(Option $(⟦t⟧))) =>
                   let m : Q(Metadata) := .fvar metadataRef
                   let t' : Q(Type) := q(Option $(⟦t⟧))
                   let m' : Expr := q($(m).boxHeap $t $a)
                   Expr.mkEq t' ρ m' }]

def match_nullable (t : SierraType) : FuncData where
  inputTypes := [.Nullable t]
  branches := [{ outputTypes := []
                 condition := fun (a : Q(Option $(⟦t⟧))) => q($a = .none) },
               { outputTypes := [.Box t]
                 condition := fun (a : Q(Option $(⟦t⟧))) (ρ : Q(Nat)) =>
                   let m : Q(Metadata) := .fvar metadataRef
                   let t' : Q(Type) := q(Option $(⟦t⟧))
                   let m' : Expr := q($(m).boxHeap $t $ρ)
                   Expr.mkEq t' a m' }]

def nullableLibfuncs (typeRefs : HashMap Identifier SierraType) : Identifier → Option FuncData
| .name "null" [.identifier ident] .none => return null (← typeRefs.find? ident)
| .name "nullable_from_box" [.identifier ident] .none =>
  return nullable_from_box metadataRef (← typeRefs.find? ident)
| .name "match_nullable" [.identifier ident] .none =>
  return match_nullable metadataRef (← typeRefs.find? ident)
| _ => .none
