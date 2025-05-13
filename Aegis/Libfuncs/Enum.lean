import Aegis.Types

open Qq Lean Sierra

namespace Sierra

/-- Generalization of `SierraBool`. The index denotes the number of `⊕`, *not* the number of fields! -/
abbrev UnitEnum : ℕ → Type
| 0 => Unit
| Nat.succ n => Unit ⊕ UnitEnum n

instance : Inhabited (UnitEnum n) :=
  ⟨match n with
  | 0 => ()
  | _ + 1 => Sum.inl ()⟩

def UnitEnum.fromIdx : (size : ℕ) → (n : ℕ) → UnitEnum size
| 0, 0 => ()
| _ + 1, 0 => Sum.inl ()
| n + 1, i + 1 => Sum.inr (.fromIdx n i)
| _, _ => panic!"foo"

end Sierra

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
  branches := fields.zipIdx.map fun (field, idx) =>
    { outputTypes := [field]
      condition := fun (a : Q($(⟦.Enum fields⟧))) ρ =>
        Expr.mkEq q($(⟦.Enum fields⟧)) (enum_selector fields idx ρ) a }

def enum_snapshot_match (fields : List SierraType) : FuncData where
  inputTypes := [.Snapshot <| .Enum fields]
  branches := fields.zipIdx.map fun (field, idx) =>
    { outputTypes :=
        [match field with
         -- TODO check if `Array` is really the only thing that gets snapshotted
         | .Array t => .Snapshot (.Array t)
         | _ => field ]
      condition := fun (a : Q($(⟦.Enum fields⟧))) ρ =>
        Expr.mkEq q($(⟦.Enum fields⟧)) (enum_selector fields idx ρ) a }

def enum_from_bounded_int (fields : List SierraType) : FuncData where
  inputTypes := [.BoundedInt 0 (fields.length - 1)]
  branches := [{ outputTypes := [.Enum fields]
                 condition := fun (a : Q(Int)) (ρ : Q($(⟦.Enum fields⟧))) =>
                   let idx : Q(Nat) := q($(a).toNat)
                   let size : Nat := fields.length - 1
                   let size : Q(Nat) := q($size)
                   Expr.mkEq q($(⟦.Enum fields⟧)) ρ q(UnitEnum.fromIdx $size $idx) }]

def enumLibfuncs (typeRefs : Std.HashMap Identifier SierraType) : Identifier → Option FuncData
| .name "enum_init" [.identifier ident, .const (.ofNat n)] .none =>
  match getMuBody <$> typeRefs[ident]? with
  | .some (.Enum fields) =>
    if hn : n < fields.length then enum_init fields ⟨n, hn⟩
    else .none
  | _ => .none
| .name "enum_match" [.identifier ident] .none =>
  match getMuBody <$> typeRefs[ident]? with
  | .some (.Enum fields) =>
    enum_match fields
  | _ => .none
| .name "enum_snapshot_match" [.identifier ident] .none =>
  match getMuBody <$> typeRefs[ident]? with
  | .some (.Enum fields) =>
    enum_snapshot_match fields
  | _ => .none
| .name "enum_from_bounded_int" [.identifier ident] .none =>
  match getMuBody <$> typeRefs[ident]? with
  | .some (.Enum fields) =>
    enum_from_bounded_int fields
  | _ => .none
| _ => .none
