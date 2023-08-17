import Aegis.FuncData.ControlFlow
import Aegis.FuncData.Felt252
import Aegis.FuncData.UInt8
import Aegis.FuncData.UInt16
import Aegis.FuncData.UInt32
import Aegis.FuncData.UInt64
import Aegis.FuncData.UInt128
import Aegis.FuncData.Bool
import Aegis.FuncData.Enum
import Aegis.FuncData.Struct
import Aegis.FuncData.Box
import Aegis.FuncData.Snapshot
import Aegis.FuncData.Array
import Aegis.FuncData.FunctionCall
import Aegis.FuncData.Hash
import Aegis.FuncData.BuiltinCosts
import Aegis.FuncData.GasBuiltin
import Aegis.FuncData.NonZero
import Aegis.FuncData.Nullable
import Aegis.FuncData.Storage
import Aegis.FuncData.Syscall
import Aegis.FuncData.ContractAddress
import Aegis.FuncData.UInt256

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
