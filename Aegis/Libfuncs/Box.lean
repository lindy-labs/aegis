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

def boxLibfuncs (typeRefs : HashMap Identifier SierraType) : Identifier → Option FuncData
| .name "into_box" [.identifier ident] _ =>
  match getMuBody <$> typeRefs.find? ident with
  | .some t => into_box metadataRef t
  | _ => .none
| .name "unbox" [.identifier ident] _ =>
  match getMuBody <$> typeRefs.find? ident with
  | .some t => unbox metadataRef t
  | _ => .none
| _ => .none
