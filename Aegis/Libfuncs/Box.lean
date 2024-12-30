import Aegis.Types

open Qq Lean Sierra

namespace Sierra.FuncData

variable (metadataRef : FVarId)

def into_box (t : SierraType) : FuncData where
  inputTypes := [t]
  branches := [{ outputTypes := [.Box t]
                 condition := fun a (ρ : Q(Nat)) =>
                   let m : Q(Metadata) := .fvar metadataRef
                   let lhs : Q(Option ($(t).toType)) := q($(m).boxHeap $t $ρ)
                   let rhs := mkAppN (mkConst `Option.some [levelZero]) #[t.toQuote, a]
                   Expr.mkEq q(Option ($(t).toType)) lhs rhs }]

def unbox (t : SierraType) : FuncData where
  inputTypes := [.Box t]
  branches := [{ outputTypes := [t]
                 condition := fun (a : Q(Nat)) (ρ : Expr) =>
                   let m : Q(Metadata) := .fvar metadataRef
                   let rhs : Q(Option ($(t).toType)) := q($(m).boxHeap $t $a)
                   let lhs := mkAppN (mkConst `Option.some [levelZero]) #[t.toQuote, ρ]
                   Expr.mkEq q(Option ($(t).toType)) lhs rhs }]

def box_forward_snapshot (t : SierraType) : FuncData where
  inputTypes := [.Snapshot (.Box t)]
  branches := [{ outputTypes := [.Box (.Snapshot t)]
                 condition := fun (a ρ : Q(Nat)) =>
                   let m : Q(Metadata) := .fvar metadataRef
                   let lhs : Expr := q($(m).boxHeap (.Snapshot $t) $ρ)
                   let rhs : Expr := q($(m).boxHeap $t $a)
                   Expr.mkEq q(Option ($(t).toType)) lhs rhs }]

def boxLibfuncs (typeRefs : Std.HashMap Identifier SierraType) : Identifier → Option FuncData
| .name "into_box" [.identifier ident] _ =>
  match getMuBody <$> typeRefs[ident]? with
  | .some t => into_box metadataRef t
  | _ => .none
| .name "unbox" [.identifier ident] _ =>
  match getMuBody <$> typeRefs[ident]? with
  | .some t => unbox metadataRef t
  | _ => .none
| .name "box_forward_snapshot" [.identifier ident] .none =>
  return box_forward_snapshot metadataRef (← typeRefs[ident]?)
| _ => .none
