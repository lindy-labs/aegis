import SierraLean.FuncDataUtil

open Qq Lean Sierra

namespace Sierra.FuncData

def array_new (t : SierraType) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [.Array t]
                 condition := fun (ρ : Q(List $t.toQuote)) => q($ρ = []) }]

def array_append (t : SierraType) : FuncData where
  inputTypes := [.Array t, t]
  branches := [{ outputTypes := [.Array t]
                 condition := fun (a b ρ : Q(List $t.toQuote)) => q($ρ = $a ++ $b) }]

def array_pop_front (t : SierraType) : FuncData where
  inputTypes := [.Array t]
  branches := [{ outputTypes := [.Array t, .Box t]
                 condition := fun (a ρ₁: Q(List $t.toQuote)) (ρ₂ : Q($t.toQuote)) =>
                   q($ρ₂ :: $ρ₁ = $a) },
               { outputTypes := [.Array t]
                 condition := fun (a : Q(List $t.toQuote)) (ρ : Q(List $t.toQuote)) =>
                   q($a = [] ∧ $ρ = []) }] -- TODO not actually clear what `ρ` is

def array_len (t : SierraType) : FuncData where
  inputTypes := [.Snapshot (.Array t)]
  branches := [{ outputTypes := [.U32]
                 condition := fun (a : Q(List $t.toQuote)) (ρ : Q(UInt128)) =>
                   q($ρ = ($a).length) }]

def array_get (t : SierraType) : FuncData where
  inputTypes := [.RangeCheck, .Snapshot (.Array t), .U32]
  branches := [{ outputTypes := [.RangeCheck, .Box t]
                 condition := fun rc (a : Q(List $t.toQuote)) (i : Q(UInt32)) rc' (ρ : Q($t.toQuote)) =>
                   q(Option.some $ρ = List.get? $a ($i).val) },
               { outputTypes := [.RangeCheck]
                 condition := fun rc (a : Q(List $t.toQuote)) (i : Q(UInt32)) rc' =>
                   q(($i).val ≥ ($a).length) }]

def arrayLibfuncs (typeRefs : HashMap Identifier SierraType) : Identifier → Option FuncData
| .name "array_new" [.identifier ident] => return array_new (← typeRefs.find? ident)
| .name "array_append" [.identifier ident] => return array_append (← typeRefs.find? ident)
| .name "array_pop_front" [.identifier ident] => return array_pop_front (← typeRefs.find? ident)
| .name "array_len" [.identifier ident] => return array_len (← typeRefs.find? ident)
| .name "array_get" [.identifier ident] => return array_get (← typeRefs.find? ident)
| _ => .none
