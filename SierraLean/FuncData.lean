import SierraLean.FuncData.ControlFlow
import SierraLean.FuncData.Felt252
import SierraLean.FuncData.UInt128
import SierraLean.FuncData.Bool

open Lean Qq

namespace Sierra.FuncData

/-- Compile-time function data registry -/
def libfuncs (i : Identifier) : Option FuncData :=
  controlFlowLibfuncs i
  <|> felt252Libfuncs i
  <|> uint128Libfuncs i
  <|> boolLibfuncs i
