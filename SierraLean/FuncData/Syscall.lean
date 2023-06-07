import SierraLean.FuncDataUtil
import Mathlib.Data.ZMod.Basic

open Qq Sierra

namespace Sierra

def SierraType.BlockInfo : SierraType :=
.Struct [.U64
        , .U64
        , .ContractAddress]

def SierraType.TxInfo : SierraType :=
.Struct [.Felt252
        , .ContractAddress
        , .U128
        , .Snapshot <| .Array .Felt252
        , .Felt252
        , .Felt252
        , .Felt252
        ]

def SierraType.ExecutionInfo : SierraType :=
.Struct [.BlockInfo, .TxInfo, .ContractAddress, .ContractAddress, .Felt252]

namespace FuncData

def pedersen : FuncData where
  inputTypes := [.Pedersen, .Felt252, .Felt252]
  branches := [{ outputTypes := [.Pedersen, .Felt252]
                 condition := fun _ _ _ _ _ => q(True) }]  --TODO

def emit_event_syscall : FuncData where
  inputTypes := [.GasBuiltin, .System, .Snapshot (.Array .Felt252), .Snapshot (.Array .Felt252)]
  branches := [{ outputTypes := [.GasBuiltin, .System]
                 condition := fun _ _ _ _ _ _ => q(True) },  -- TODO
               { outputTypes := [.GasBuiltin, .System, .Array .Felt252]
                 condition := fun _ _ _ _ _ _ _ => q(True) }]

def get_execution_info_syscall : FuncData where
  inputTypes := [.GasBuiltin, .System]
  branches := [{ outputTypes := [.GasBuiltin, .System, .Box <| .ExecutionInfo]
                 condition := fun _ _ _ _ _ => q(True) },  -- TODO
               { outputTypes := [.GasBuiltin, .System, .Array .Felt252]
                 condition := fun _ _ _ _ _ => q(True) }]  -- TODO

def hashLibfuncs : Identifier → Option FuncData
| .name "pedersen" [] .none => pedersen
| .name "emit_event_syscall" [] .none => emit_event_syscall
| .name "get_execution_info_syscall" [] .none => get_execution_info_syscall
| _                         => .none
