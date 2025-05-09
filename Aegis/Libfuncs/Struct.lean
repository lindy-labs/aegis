import Aegis.Types

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

def struct_snapshot_deconstruct (fields : List SierraType) : FuncData where
  inputTypes := [.Snapshot <| .Struct fields]
  branches := [{ outputTypes := fields.map fun
                 -- TODO check if really only `Array`s are snapshotted
                 | .Array t => .Snapshot <| .Array t
                 | field => field
                 -- TODO This is a bit dirty, just copies the condition of `struct_deconstruct`
                 condition := fun a => OfInputs.abstract fun as =>
                   OfInputs.apply (OfInputs.map (fun ρ => Expr.mkEq q($(⟦.Struct fields⟧)) ρ a)
                   (struct_deconstruct_condition fields)) as }]

def structLibfuncs (typeRefs : Std.HashMap Identifier SierraType) : Identifier → Option FuncData
| .name "struct_construct" [.identifier ident] _ =>
  match getMuBody <$> typeRefs[ident]? with
  | .some (.Struct fields) => struct_construct fields
  | _ => .none
| .name "struct_deconstruct" [.identifier ident] _ =>
  match getMuBody <$> typeRefs[ident]? with
  | .some (.Struct fields) => struct_deconstruct fields
  | _ => .none
| .name "struct_snapshot_deconstruct" [.identifier ident] _ =>
  match getMuBody <$> typeRefs[ident]? with
  | .some (.Struct fields) => struct_snapshot_deconstruct fields
  | _ => .none
| _ => .none
