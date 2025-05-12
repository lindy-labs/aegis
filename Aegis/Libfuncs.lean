import Aegis.Libfuncs.ControlFlow
import Aegis.Libfuncs.Felt252
import Aegis.Libfuncs.UInt8
import Aegis.Libfuncs.UInt16
import Aegis.Libfuncs.UInt32
import Aegis.Libfuncs.UInt64
import Aegis.Libfuncs.UInt128
import Aegis.Libfuncs.Int8
import Aegis.Libfuncs.Int16
import Aegis.Libfuncs.Int32
import Aegis.Libfuncs.Int64
import Aegis.Libfuncs.Int128
import Aegis.Libfuncs.Bytes31
import Aegis.Libfuncs.Bool
import Aegis.Libfuncs.Enum
import Aegis.Libfuncs.Struct
import Aegis.Libfuncs.Box
import Aegis.Libfuncs.Snapshot
import Aegis.Libfuncs.Array
import Aegis.Libfuncs.FunctionCall
import Aegis.Libfuncs.Hash
import Aegis.Libfuncs.BuiltinCosts
import Aegis.Libfuncs.GasBuiltin
import Aegis.Libfuncs.NonZero
import Aegis.Libfuncs.Nullable
import Aegis.Libfuncs.Storage
import Aegis.Libfuncs.Syscall
import Aegis.Libfuncs.ContractAddress
import Aegis.Libfuncs.UInt256
import Aegis.Libfuncs.Casts
import Aegis.Libfuncs.Const
import Aegis.Libfuncs.BoundedInt

open Lean Qq

namespace Sierra.FuncData

variable (currentFunc : Identifier) (typeRefs : Std.HashMap Identifier SierraType)
  (specs : Std.HashMap Identifier (Name × (FVarId → FuncData)))  (metadataRef : FVarId)
  (i : Identifier)

/-- The definition of `libfuncs` is split into pieces due to slow elaboration time. -/
private def libfuncs_aux :=
  controlFlowLibfuncs typeRefs i
  <|> felt252Libfuncs i
  <|> uint128Libfuncs i
  <|> boolLibfuncs i
  <|> enumLibfuncs typeRefs i
  <|> structLibfuncs typeRefs i
  <|> boxLibfuncs metadataRef typeRefs i
  <|> snapshotLibfuncs typeRefs i
  <|> nonZeroLibfuncs typeRefs i

private def libfuncs_aux2 :=
  libfuncs_aux typeRefs metadataRef i
  <|> arrayLibfuncs metadataRef typeRefs i
  <|> functionCallLibfuncs specs metadataRef i
  <|> syscallLibfuncs metadataRef i
  <|> builtinCostsLibfuncs currentFunc metadataRef i
  <|> gasBuiltinLibfuncs currentFunc metadataRef i
  <|> uint8Libfuncs i
  <|> hashLibfuncs metadataRef i

private def libfuncs_aux3 :=
  libfuncs_aux2 currentFunc typeRefs specs metadataRef i
  <|> int8Libfuncs i
  <|> int16Libfuncs i
  <|> int32Libfuncs i
  <|> int64Libfuncs i
  <|> int128Libfuncs i
  <|> bytes31Libfuncs i
  <|> boundedIntLibfuncs typeRefs i

/-- Compile-time function data registry -/
def libfuncs : Option FuncData :=
  libfuncs_aux3 currentFunc typeRefs specs metadataRef i
  <|> uint16Libfuncs i
  <|> uint32Libfuncs i
  <|> uint64Libfuncs i
  <|> uint256Libfuncs i
  <|> nullableLibfuncs metadataRef typeRefs i
  <|> storageLibfuncs i
  <|> contractAddressLibfuncs i
  <|> castsLibfuncs i
  <|> constLibfuncs metadataRef typeRefs i
