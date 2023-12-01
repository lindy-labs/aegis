import Aegis.Types

open Qq Lean Sierra

namespace Sierra.FuncData

variable (metadataRef : FVarId)

def box_into (t : SierraType) : FuncData where
  inputTypes := [t]
  branches := [{ outputTypes := [.Box t]
                 condition := fun a (ρ : Q(Nat)) =>
                   let m : Q(Metadata) := .fvar metadataRef
                   let lhs : Q(Option ($(t).toType)) := q($(m).boxHeap $t $ρ)
                   let rhs : Expr := mkAppN (mkConst `Option.some) #[q(Option ($(t).toType)), a]
                   Expr.mkEq q(Option ($(t).toType)) lhs rhs }]

def unbox (t : SierraType) : FuncData where
  inputTypes := [.Box t]
  branches := [{ outputTypes := [t]
                 condition := fun (a : Q(Nat)) (ρ : Expr) =>
                   let m : Q(Metadata) := .fvar metadataRef
                   let rhs : Q(Option ($(t).toType)) := q($(m).boxHeap $t $a)
                   let lhs : Expr := mkAppN (mkConst `Option.some) #[q(Option ($(t).toType)), ρ]
                   Expr.mkEq q(Option ($(t).toType)) lhs rhs }]

def boxLibfuncs (typeRefs : HashMap Identifier SierraType) : Identifier → Option FuncData
| .name "box_into" [.identifier ident] _ =>
  match typeRefs.find? ident with
  | .some t => box_into metadataRef t
  | _ => .none
| .name "unbox" [.identifier ident] _ =>
  match typeRefs.find? ident with
  | .some t => unbox metadataRef t
  | _ => .none
| _ => .none
