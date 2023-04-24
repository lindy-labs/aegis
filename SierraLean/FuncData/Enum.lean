import SierraLean.FuncDataUtil

open Qq Lean Sierra

namespace Sierra.FuncData

def enum_init (fields : List SierraType) (idx : Fin fields.length) : FuncData where
  inputTypes := [fields.get idx]
  branches := [{
    outputTypes := [.Enum fields],
    condition := fun a (ρ : Q($(enum <| fields.map SierraType.toQuote))) =>
      Expr.mkAnds [Expr.mkEq q(ℕ) q($ρ.1.val) (toExpr idx.val),
        Expr.mkEq q($(SierraType.toQuote <| fields.get idx)) q($ρ.2) q($a)]
  }]

def enum_match (fields : List SierraType) : FuncData where
  inputTypes := [.Enum fields]
  branches := fields.enum.map fun (idx, field) =>
    { outputTypes := [field]
      condition := fun (a : Q($(enum <| fields.map SierraType.toQuote))) ρ =>
        Expr.mkAnds [Expr.mkEq q(ℕ) q($idx) q($a.1.val),
          Expr.mkEq q($(SierraType.toQuote <| fields.get! idx)) q($ρ) q($a.2)] }

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
