import Aegis.Types

open Qq Lean Sierra

namespace Sierra.FuncData

variable (metadataRef : FVarId)

def array_new (t : SierraType) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [.Array t]
                 condition := fun (ρ : Q(List $t.toQuote)) => q($ρ = []) }]

def array_append (t : SierraType) : FuncData where
  inputTypes := [.Array t, t]
  branches := [{ outputTypes := [.Array t]
                 condition := fun (a : Q(List $t.toQuote)) (b : Q($t.toQuote))
                   (ρ : Q(List $t.toQuote)) => q($ρ = $a ++ [$b]) }]

example (f : Bool → Q(Type)) (b : Bool) (a b : Q(List $(f b))) : Q(Prop) :=
  q(∃ x, x :: $a = $b)

def array_pop_front_aux (T : Q(Type)) (m' : Q(Option $T)) (a ρ₁ : Q(List $T)) : Q(Prop) :=
  q(∃ ρ₂', $m' = .some ρ₂' ∧ ρ₂' :: $ρ₁ = $a)

def array_pop_front (t : SierraType) : FuncData where
  inputTypes := [.Array t]
  branches := [{ outputTypes := [.Array t, .Box t]
                 condition :=
                   fun a ρ₁ (ρ₂ : Q(Nat)) =>
                   let m : Q(Metadata) := .fvar metadataRef
                   let m' : Expr := q($(m).boxHeap $t $ρ₂)
                   array_pop_front_aux ⟦t⟧ m' a ρ₁ },
               { outputTypes := [.Array t]
                 condition := fun (a : Q(List $t.toQuote)) (ρ : Q(List $t.toQuote)) =>
                   q($a = [] ∧ $ρ = []) }] -- TODO maybe add possibility of box being empty

def array_len (t : SierraType) : FuncData where
  inputTypes := [.Snapshot (.Array t)]
  branches := [{ outputTypes := [.U32]
                 condition := fun (a : Q(List $t.toQuote)) (ρ : Q(UInt32)) =>
                   q($ρ = ($a).length) }]

def array_get (t : SierraType) : FuncData where
  inputTypes := [.RangeCheck, .Snapshot (.Array t), .U32]
  branches := [{ outputTypes := [.RangeCheck, .Box t]
                 condition := fun _ (a : Q(List $t.toQuote)) (i : Q(UInt32)) _ (ρ : Q($t.toQuote)) =>
                   q(Option.some $ρ = List.get? $a ($i).val) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(List $t.toQuote)) (i : Q(UInt32)) _ =>
                   q(($i).val ≥ ($a).length) }]

def array_snapshot_pop_front (t : SierraType) : FuncData where
  inputTypes := [.Snapshot (.Array t)]
  branches := [{ outputTypes := [.Snapshot (.Array t), .Box t]
                 condition :=
                   fun a ρ₁ (ρ₂ : Q(Nat)) =>
                   let m : Q(Metadata) := .fvar metadataRef
                   let m' : Expr := q($(m).boxHeap $t $ρ₂)
                   array_pop_front_aux ⟦t⟧ m' a ρ₁ },
               { outputTypes := [.Snapshot (.Array t)]
                 condition := fun (a ρ : Q(List $(⟦t⟧))) =>
                   q($a = [] ∧ $ρ = []) }]

def arrayLibfuncs (typeRefs : HashMap Identifier SierraType) : Identifier → Option FuncData
| .name "array_new" [.identifier ident] .none =>
  return array_new (← typeRefs.find? ident)
| .name "array_append" [.identifier ident] .none =>
  return array_append (← typeRefs.find? ident)
| .name "array_pop_front" [.identifier ident] .none =>
  return array_pop_front metadataRef (← typeRefs.find? ident)
| .name "array_len" [.identifier ident] .none =>
  return array_len (← typeRefs.find? ident)
| .name "array_get" [.identifier ident] .none =>
  return array_get (← typeRefs.find? ident)
| .name "array_snapshot_pop_front" [.identifier ident] .none =>
  return array_snapshot_pop_front metadataRef (← typeRefs.find? ident)
| _ => .none
