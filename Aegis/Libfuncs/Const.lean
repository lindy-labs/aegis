import Aegis.Types

open Qq Sierra.SierraType Lean

namespace Sierra.FuncData

variable (typeRefs : HashMap Identifier SierraType)

def const_quote_of_num (ty : SierraType) (val : ℤ) : Q($(⟦ty⟧)) :=
match ty with
| .Felt252 => (q($val) : Q(Sierra.F))
| .U8 => (q($val) : Q(Sierra.UInt8))
| .U16 => (q($val) : Q(Sierra.UInt16))
| .U32 => (q($val) : Q(Sierra.UInt32))
| .U64 => (q($val) : Q(Sierra.UInt64))
| .U128 => (q($val) : Q(Sierra.UInt128))
| _ => panic "no conversion from object level `Nat` to numeral Sierra type found!"

-- Const<Tuple<felt252, felt252, felt252>, Const<felt252, 10>, Const<felt252, 20>, Const<felt252, 30>>

def mkProd (α β : Q(Type)) (a : Q($α)) (b : Q($β)) : Q($α × $β) := q(($a, $b))

def mkTuple (ty : Q(Type)) (vals : List Expr) : Expr :=
match vals with
| [] => (q(()) : Q(Unit))
| [v] => v
| (v::vs) =>
  match Expr.prod? ty with
  | .some (tyfst, tysnd) =>
    mkProd tyfst tysnd v <| mkTuple tysnd vs
  | _ => panic "foo"

partial def const_quote_of_struct (ty : SierraType) (vals : List SierraType) : Q($(⟦ty⟧)) :=
match ty with
| .Struct _ =>
  let vals : List Expr := vals.map fun v =>
  match v with
  | .ConstNum t v => const_quote_of_num t v
  | .ConstStruct t vs => const_quote_of_struct t vs
  | _ => panic "field of a composite constant must be a constant"
  mkTuple ⟦ty⟧ vals
| _ => panic "composite constant must be a struct!"

def const_num_as_immediate (ty : SierraType) (val : ℤ) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [ty]
                 condition := fun (a : Q($(⟦ty⟧))) =>
                   Expr.mkEq q($(⟦ty⟧)) a (const_quote_of_num ty val) }]

def const_struct_as_immediate (ty : SierraType) (vals : List SierraType) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [ty]
                 condition := fun (a : Q($(⟦ty⟧))) =>
                  Expr.mkEq q($(⟦ty⟧)) a (const_quote_of_struct ty vals) }]

def constLibfuncs : Identifier → Option FuncData
| .name "const_as_immediate" [.identifier ident] .none => do
  match ← typeRefs.find? ident with
  | .ConstNum ty val => .some <| const_num_as_immediate ty val
  | .ConstStruct ty vals => .some <| const_struct_as_immediate ty vals
  | _ => .none
| _ => .none
