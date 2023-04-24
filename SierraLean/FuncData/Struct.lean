import SierraLean.FuncDataUtil

open Qq Lean Sierra

namespace Sierra.FuncData

private def struct_construct_condition {l} (fields : List (Fin l × SierraType))
   (fields' : List SierraType) (acc : Expr → Expr := id) :
    OfInputs Q(Prop) (List.map SierraType.toQuote (fields.map (·.2) ++ [SierraType.Struct fields'])) :=
match fields with
| [] => fun (ρ : Expr) => acc ρ
| ((idx, field) :: fields) => fun a =>
  let acc' : Expr → Expr := fun ρ =>
    Expr.mkAnds [acc ρ, Expr.mkEq (SierraType.toQuote field) (mkApp ρ q($idx)) a]
  struct_construct_condition fields fields' acc'

def struct_construct (fields : List SierraType) : FuncData where
  inputTypes := fields
  branches := [{ outputTypes := [.Struct fields]
                 condition := List.map_of_enumFin fields ▸
                  struct_construct_condition fields.enumFin (Prod.snd <$> fields.enumFin) }]

def structLibFuncs (typeRefs : HashMap Identifier SierraType) : Identifier → Option FuncData
| .name "struct_construct" [.identifier ident] =>
  match typeRefs.find? ident with
  | .some (.Struct fields) => struct_construct fields
  | _ => .none
| _ => .none

