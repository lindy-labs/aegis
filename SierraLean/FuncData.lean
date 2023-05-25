import SierraLean.FuncData.ControlFlow
import SierraLean.FuncData.Felt252
import SierraLean.FuncData.UInt8
import SierraLean.FuncData.UInt128
import SierraLean.FuncData.Bool
import SierraLean.FuncData.Enum
import SierraLean.FuncData.Struct
import SierraLean.FuncData.Box
import SierraLean.FuncData.Snapshot
import SierraLean.FuncData.Array
import SierraLean.FuncData.FunctionCall
import SierraLean.FuncData.Hash
import SierraLean.FuncData.BuiltinCosts
import SierraLean.FuncData.GasBuiltin

open Lean Qq

namespace Sierra.FuncData

def foo1 : Nat → Option Nat
| 1 => .some 6
| _ => .none
def foo2 : Nat → Option Nat
| 1 => .some 6
| _ => .none
def foo3 : Nat → Option Nat
| 1 => .some 6
| _ => .none
def foo4 : Nat → Option Nat
| 1 => .some 6
| _ => .none
def foo5 : Nat → Option Nat
| 1 => .some 6
| _ => .none
def foo6 : Nat → Option Nat
| 1 => .some 6
| _ => .none
def foo7 : Nat → Option Nat
| 1 => .some 6
| _ => .none
def foo8 : Nat → Option Nat
| 1 => .some 6
| _ => .none
def foo9 : Nat → Option Nat
| 1 => .some 6
| _ => .none
def foo10 : Nat → Option Nat
| 1 => .some 6
| _ => .none
def foo11 : Nat → Option Nat
| 1 => .some 6
| _ => .none
def foo12 : Nat → Option Nat
| 1 => .some 6
| _ => .none
def foo13 : Nat → Option Nat
| 1 => .some 6
| _ => .none

/-- The definition of `libfuncs` is split into pieces do to slow elaboration time. -/
private def libfuncs_aux (typeRefs : HashMap Identifier SierraType)
    (i : Identifier) :=
  controlFlowLibfuncs typeRefs i
  <|> felt252Libfuncs i
  <|> uint128Libfuncs i
  <|> boolLibfuncs i
  <|> enumLibfuncs typeRefs i
  <|> structLibfuncs typeRefs i
  <|> boxLibfuncs typeRefs i
  <|> snapshotLibfuncs typeRefs i

/-- Compile-time function data registry -/
def libfuncs (typeRefs : HashMap Identifier SierraType)
    (specs : HashMap Identifier (Name × (FVarId → FuncData)))
    (metadataRef : FVarId)
    (i : Identifier) :
    Option FuncData :=
  libfuncs_aux typeRefs i
  <|> arrayLibfuncs typeRefs i
  <|> functionCallLibfuncs specs metadataRef i
  <|> hashLibfuncs i
  <|> builtinCostsLibfuncs i
  <|> gasBuiltinLibfuncs i
  <|> uint8Libfuncs i
