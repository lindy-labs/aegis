import Aegis.Types

open Qq Sierra.SierraType

namespace Sierra.FuncData

def bytes31_const (n : Q(Bytes31)) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [.Bytes31]
                 condition := fun (ρ : Q(Bytes31)) => q($ρ = $n) }]

def bytes31_try_from_felt252 : FuncData where
  inputTypes := [.RangeCheck, .Felt252]
  branches := [{ outputTypes := [.RangeCheck, .Bytes31]
                 condition := fun _ (a : Q(F)) _ (ρ : Q(Bytes31)) =>
                   q($(a).val < 452312848583266388373324160190187140051835877600158453279131187530910662656 ∧ $ρ = $(a).val) },
               { outputTypes := [.RangeCheck]
                 condition := fun _ (a : Q(F)) _ => q(452312848583266388373324160190187140051835877600158453279131187530910662656 ≤ $(a).val) }]

def bytes31_to_felt252 : FuncData where
  inputTypes := [.Bytes31]
  branches := [{ outputTypes := [.Felt252]
                 condition := fun (a : Q(Bytes31)) (ρ : Q(F)) =>
                   Expr.mkEq q(F) ρ
                     q(Fin.castLE (m := PRIME) (by simp [PRIME]) $(a).toFin) }]

def bytes31Libfuncs : Identifier → Option FuncData
| .name "bytes31_const" [.const n] .none    => bytes31_const (Lean.toExpr (α := BitVec 248) n)
| .name "bytes31_try_from_felt252" [] .none => bytes31_try_from_felt252
| .name "bytes31_to_felt252" [] .none       => bytes31_to_felt252
| _                                         => .none
