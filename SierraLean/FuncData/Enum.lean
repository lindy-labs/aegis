import SierraLean.FuncDataUtil

open Qq Lean Sierra

namespace Sierra.FuncData

private def enum_selector (fields : List SierraType) (idx : ℕ) (a : Expr) : Expr :=
match fields, idx with
| [], _          => q(())
| [_], 0         => a
| t::ts, 0       => mkAppN (mkConst ``Sum.inl [levelZero, levelZero]) #[q($(⟦t⟧)), q($(⟦.Enum ts⟧)), a]
| t::ts, .succ n => let x : Expr := enum_selector ts n a;
                    mkAppN (mkConst ``Sum.inr [levelZero, levelZero]) #[q($(⟦t⟧)), q($(⟦.Enum ts⟧)), x]

def enum_init (fields : List SierraType) (idx : Fin fields.length) : FuncData where
  inputTypes := [fields.get idx]
  branches := [{
    outputTypes := [.Enum fields],
    condition := fun a (ρ : Q($(⟦.Enum fields⟧))) =>
      Expr.mkEq q($(⟦.Enum fields⟧)) ρ (enum_selector fields idx.val a) }]

def enum_match (fields : List SierraType) : FuncData where
  inputTypes := [.Enum fields]
  branches := fields.enum.map fun (idx, field) =>
    { outputTypes := [field]
      condition := fun (a : Q($(⟦.Enum fields⟧))) ρ =>
        Expr.mkEq q($(⟦.Enum fields⟧)) (enum_selector fields idx ρ) a }

def enumLibfuncs (typeRefs : HashMap Identifier SierraType) : Identifier → Option FuncData
| .name "enum_init" [.identifier ident, .const (.ofNat n)] =>
  match typeRefs.find? ident with
  | .some (.Enum fields) =>
    if hn : n < fields.length then enum_init fields ⟨n, hn⟩
    else .none
  | _ => .none
| .name "enum_match" [.identifier ident] =>
  match typeRefs.find? ident with
  | .some (.Enum fields) => enum_match fields
  | _ => .none
| _ => .none
