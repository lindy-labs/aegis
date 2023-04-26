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
                 condition := fun (a : Q(List $t.toQuote))
                                (b : Q($t.toQuote))
                                (ρ : Q(List $t.toQuote)) => q($ρ = $a ++ [$b]) }]

def array_pop_front (t : SierraType) : FuncData where
  inputTypes := [.Array t]
  branches := [{ outputTypes := [.Array t, .Box t]
                 condition := fun (a ρ₁: Q(List $t.toQuote)) (ρ₂ : Q($t.toQuote)) =>
                   q($ρ₂ :: $ρ₁ = $a) },
               { outputTypes := [.Array t]
                 condition := fun (a : Q(List $t.toQuote)) (ρ : Q(List $t.toQuote)) =>
                   q(False) }] -- TODO

def arrayLibfuncs (typeRefs : HashMap Identifier SierraType) : Identifier → Option FuncData
| .name "array_new" [.identifier ident] => return array_new (← typeRefs.find? ident)
| .name "array_append" [.identifier ident] => return array_append (← typeRefs.find? ident)
| .name "array_pop_front" [.identifier ident] => return array_pop_front (← typeRefs.find? ident)
| _ => .none
