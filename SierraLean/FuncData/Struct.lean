import SierraLean.FuncDataUtil

open Qq Lean Sierra

namespace Sierra.FuncData

private def struct_construct_condition (fields : List (Fin l × SierraType))
  (fields' : List SierraType) (acc : Expr → Expr := fun _ => q(True)) :
    OfInputs Q(Prop) (SierraType.toQuote <$> (fields.map (·.2) ++ [.Struct fields'])) :=
match fields with
| [] => fun (ρ : Expr) => acc ρ
| ((idx, field) :: fields) => fun a =>
  struct_construct_condition fields fields' fun ρ =>
    Expr.mkAnds [acc ρ, Expr.mkEq field.toQuote (mkApp ρ q($idx)) a]

def struct_construct (fields : List SierraType) : FuncData where
  inputTypes := fields
  branches := [{ outputTypes := [.Struct fields]
                 condition := List.map_of_enumFin fields ▸
                  struct_construct_condition fields.enumFin (Prod.snd <$> fields.enumFin) }]

private def struct_deconstruct_condition (fields : List (Fin l × SierraType))
  (fields' : List SierraType) (a : Expr) (acc : Expr := q(True)):
    OfInputs Q(Prop) (SierraType.toQuote <$> (fields.map (·.2))) :=
match fields with
| [] => acc
| ((idx, field) :: fields) => fun ρ =>
    let acc' := Expr.mkAnds [acc, Expr.mkEq field.toQuote ρ (mkApp a q($idx))]
    struct_deconstruct_condition fields fields' ρ acc'

def struct_deconstruct (fields : List SierraType) : FuncData where
  inputTypes := [.Struct fields]
  branches := [{ outputTypes := fields
                 condition := List.map_of_enumFin fields ▸
                  struct_deconstruct_condition fields.enumFin (Prod.snd <$> fields.enumFin) }]

def structLibfuncs (typeRefs : HashMap Identifier SierraType) : Identifier → Option FuncData
| .name "struct_construct" [.identifier ident] =>
  match typeRefs.find? ident with
  | .some (.Struct fields) => struct_construct fields
  | _ => .none
| .name "struct_deconstruct" [.identifier ident] =>
  match typeRefs.find? ident with
  | .some (.Struct fields) => struct_deconstruct fields
  | _ => .none
| _ => .none
