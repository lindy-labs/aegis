import SierraLean.FuncData.ControlFlow
import SierraLean.FuncData.Felt252
import SierraLean.FuncData.UInt128
import SierraLean.FuncData.Bool
import SierraLean.FuncData.Enum
import SierraLean.FuncData.Struct

open Lean Qq

namespace Sierra.FuncData

/-- Compile-time function data registry -/
def libfuncs (typeRefs : HashMap Identifier SierraType) (i : Identifier) :
    Option FuncData :=
  controlFlowLibfuncs i
  <|> felt252Libfuncs i
  <|> uint128Libfuncs i
  <|> boolLibfuncs i
  <|> enumLibfuncs typeRefs i
  <|> structLibFuncs typeRefs i
