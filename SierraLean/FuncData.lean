import SierraLean.FuncData.ControlFlow
import SierraLean.FuncData.Felt252
import SierraLean.FuncData.UInt128
import SierraLean.FuncData.Bool
import SierraLean.FuncData.Enum
import SierraLean.FuncData.Struct
import SierraLean.FuncData.Box
import SierraLean.FuncData.Snapshot
import SierraLean.FuncData.Array
import SierraLean.FuncData.FunctionCall
import SierraLean.FuncData.Hash

open Lean Qq

namespace Sierra.FuncData

/-- Compile-time function data registry -/
def libfuncs (typeRefs : HashMap Identifier SierraType)
    (specs : HashMap Identifier (Name × FuncData)) (i : Identifier) :
    Option FuncData :=
  controlFlowLibfuncs typeRefs i
  <|> felt252Libfuncs i
  <|> uint128Libfuncs i
  <|> boolLibfuncs i
  <|> enumLibfuncs typeRefs i
  <|> structLibfuncs typeRefs i
  <|> boxLibfuncs typeRefs i
  <|> snapshotLibfuncs typeRefs i
  <|> arrayLibfuncs typeRefs i
  <|> functionCallLibfuncs specs i
  <|> hashLibfuncs i
