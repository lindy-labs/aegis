import Aegis.Types

open Qq Sierra.SierraType

namespace Sierra

def SierraType.minBound : SierraType → Int
| I8 => -128
| I16 => -32768
| I32 => -2147483648
| I64 => -9223372036854775808
| I128 => -170141183460469231731687303715884105728
| BoundedInt min _ => min
| _ => 0

def SierraType.maxBound : SierraType → Int
| I8 => 127
| I16 => 32767
| I32 => 2147483647
| I64 => 9223372036854775807
| I128 => 170141183460469231731687303715884105727
| U8 => 255
| U16 => 65535
| U32 => 4294967295
| U64 => 18446744073709551615
| U128 => 340282366920938463463374607431768211455
| Felt252 => 3618502788666131213697322783095070105623107215331596699973092056135872020480
| BoundedInt _ max => max
| _ => 0

def SierraType.toFelt : (ty : SierraType) → Lean.Expr → Q(F)
| I8, (val : Q(Int8)) => q($(val).toInt)
| I16, (val : Q(Int16)) => q($(val).toInt)
| I32, (val : Q(Int32)) => q($(val).toInt)
| I64, (val : Q(Int64)) => q($(val).toInt)
| I128, (val : Q(Int128)) => q($(val).toInt)
| U8, (val : Q(UInt8)) => q($(val).toNat)
| U16, (val : Q(UInt16)) => q($(val).toNat)
| U32, (val : Q(UInt32)) => q($(val).toNat)
| U64, (val : Q(UInt64)) => q($(val).toNat)
| U128, (val : Q(UInt128)) => q($(val).toNat)
| Felt252, val
| BoundedInt _ _, val => val
| _, _ => q(0)

namespace FuncData

def bounded_int_add (ty1 ty2 : SierraType) : FuncData where
  inputTypes := [ty1, ty2]
  branches := [{ outputTypes := [BoundedInt (ty1.minBound + ty2.minBound) (ty1.maxBound + ty2.maxBound)]
                 condition := fun (a b : Lean.Expr) (ρ : Q(F)) =>
                   q($ρ = $(ty1.toFelt a) + $(ty2.toFelt b)) }]

def bounded_int_sub (ty1 ty2 : SierraType) : FuncData where
  inputTypes := [ty1, ty2]
  branches := [{ outputTypes := [BoundedInt (ty1.minBound - ty2.minBound) (ty1.maxBound - ty2.maxBound)]
                 condition := fun (a b : Lean.Expr) (ρ : Q(F)) =>
                   q($ρ = $(ty1.toFelt a) - $(ty2.toFelt b)) }]

def bounded_int_mul (ty1 ty2 : SierraType) : FuncData where
  inputTypes := [ty1, ty2]
  branches := [{ outputTypes := [BoundedInt (min (ty1.minBound * ty2.minBound) <|
                                             min (ty1.minBound * ty2.maxBound) <|
                                             min (ty1.maxBound * ty2.minBound) <|
                                                 (ty1.maxBound * ty2.maxBound))
                                            (max (ty1.minBound * ty2.minBound) <|
                                             max (ty1.minBound * ty2.maxBound) <|
                                             max (ty1.maxBound * ty2.minBound) <|
                                                 (ty1.maxBound * ty2.maxBound))]
                 condition := fun (a b : Lean.Expr) (ρ : Q(F)) =>
                   q($ρ = $(ty1.toFelt a) * $(ty2.toFelt b)) }]

-- TODO fix implementation for `Nonzero<T>`
def boundedIntLibfuncs (typeRefs : Std.HashMap Identifier SierraType) : Identifier → Option FuncData
| .name "bounded_int_add" [.identifier i1, .identifier i2] .none => do
  let ty1 ← typeRefs[i1]?
  let ty2 ← typeRefs[i2]?
  .some <| bounded_int_add ty1 ty2
| .name "bounded_int_sub" [.identifier i1, .identifier i2] .none => do
  let ty1 ← typeRefs[i1]?
  let ty2 ← typeRefs[i2]?
  .some <| bounded_int_sub ty1 ty2
| .name "bounded_int_mul" [.identifier i1, .identifier i2] .none => do
  let ty1 ← typeRefs[i1]?
  let ty2 ← typeRefs[i2]?
  .some <| bounded_int_mul ty1 ty2
| _ => .none
