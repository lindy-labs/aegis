import SierraLean.FuncDataUtil
import Mathlib.Data.ZMod.Basic

open Qq Sierra

namespace Sierra

def SierraType.BlockInfo : SierraType :=
.Struct [ .U64  -- block number
        , .U64  -- block timestamp
        , .ContractAddress ]  -- sequencer address

def SierraType.TxInfo : SierraType :=
.Struct [ .Felt252  -- transaction version
        , .ContractAddress  -- the account contract from which this tx originates
        , .U128  -- max fee
        , .Snapshot <| .Array .Felt252 -- signature of the tx
        , .Felt252  -- transaction hash
        , .Felt252  -- identifier of the chain
        , .Felt252  -- nonce
        ]

def SierraType.ExecutionInfo : SierraType :=
.Struct [ .BlockInfo
        , .TxInfo
        , .ContractAddress  -- caller address
        , .ContractAddress  -- contract address
        , .Felt252  -- entry point selector
        ]

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
