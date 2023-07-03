import SierraLean.FuncData.ControlFlow
import SierraLean.FuncData.Felt252
import SierraLean.FuncData.UInt8
import SierraLean.FuncData.UInt16
import SierraLean.FuncData.UInt32
import SierraLean.FuncData.UInt64
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
import SierraLean.FuncData.NonZero
import SierraLean.FuncData.Nullable
import SierraLean.FuncData.Storage
import SierraLean.FuncData.Syscall
import SierraLean.FuncData.ContractAddress
import SierraLean.FuncData.UInt256

open Lean Qq

namespace Sierra.FuncData

variable (currentFunc : Identifier) (typeRefs : HashMap Identifier SierraType)
  (specs : HashMap Identifier (Name × (FVarId → FuncData)))  (metadataRef : FVarId)
  (i : Identifier) 

/-- The definition of `libfuncs` is split into pieces do to slow elaboration time. -/
private def libfuncs_aux :=
  controlFlowLibfuncs typeRefs i
  <|> felt252Libfuncs i
  <|> uint128Libfuncs i
  <|> boolLibfuncs i
  <|> enumLibfuncs typeRefs i
  <|> structLibfuncs typeRefs i
  <|> boxLibfuncs typeRefs i
  <|> snapshotLibfuncs typeRefs i
  <|> nonZeroLibfuncs typeRefs i

private def libfuncs_aux2 :=
  libfuncs_aux typeRefs i
  <|> arrayLibfuncs typeRefs i
  <|> functionCallLibfuncs specs metadataRef i
  <|> syscallLibfuncs metadataRef i
  <|> builtinCostsLibfuncs currentFunc metadataRef i
  <|> gasBuiltinLibfuncs i
  <|> uint8Libfuncs i
  <|> hashLibfuncs metadataRef i

/-- Compile-time function data registry -/
def libfuncs :
    Option FuncData :=
  libfuncs_aux2 currentFunc typeRefs specs metadataRef i
  <|> uint16Libfuncs i
  <|> uint32Libfuncs i
  <|> uint64Libfuncs i
  <|> uint256Libfuncs i
  <|> nullableLibfuncs typeRefs i
  <|> storageLibfuncs i
  <|> contractAddressLibfuncs i
