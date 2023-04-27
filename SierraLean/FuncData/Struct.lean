import SierraLean.FuncDataUtil

open Qq Lean Sierra

namespace Sierra.FuncData

private def struct_construct_condition (fields fields' : List SierraType) :
  OfInputs (Expr × Expr) (SierraType.toQuote <$> (fields ++ [.Struct fields'])) :=
match fields with
| [] => fun (ρ : Expr) => (ρ, q(()))
| [_] => fun (a ρ : Expr) => (ρ, a)
| t::ts => fun (a : Expr) => OfInputs.abstract fun as =>
  let tl := OfInputs.apply (struct_construct_condition ts fields') as
  (tl.1, mkAppN q(@Prod.mk.{0, 0}) #[q($(⟦t⟧)), q($(⟦.Struct ts⟧)), a, tl.2])

def struct_construct (fields : List SierraType) : FuncData where
  inputTypes := fields
  branches := [{ outputTypes := [.Struct fields]
                 condition := OfInputs.map (fun (ρ, a) => Expr.mkEq q($(⟦.Struct fields⟧)) ρ a)
                   (struct_construct_condition fields fields) }]

private def struct_deconstruct_condition (fields : List SierraType) :
  OfInputs Expr (SierraType.toQuote <$> fields) :=
match fields with
| [] => q(())
| [_] => fun (a : Expr) => a
| t::ts => fun (a : Expr) => OfInputs.abstract fun as =>
  let tl := OfInputs.apply (struct_deconstruct_condition ts) as
  mkAppN q(@Prod.mk.{0, 0}) #[q($(⟦t⟧)), q($(⟦.Struct ts⟧)), a, tl]

def struct_deconstruct (fields : List SierraType) : FuncData where
  inputTypes := [.Struct fields]
  branches := [{ outputTypes := fields
                 condition := fun a => OfInputs.map (fun ρ => Expr.mkEq q($(⟦.Struct fields⟧)) ρ a)
                   (struct_deconstruct_condition fields) }]

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
