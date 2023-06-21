import SierraLean.FuncDataUtil
import Mathlib.Data.ZMod.Basic

open Qq Sierra Lean

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

variable (metadataRef : FVarId)

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

def storage_read_syscall : FuncData where
  inputTypes := [.GasBuiltin, .System, .U32, .StorageAddress]
  branches := [{ outputTypes := [.GasBuiltin, .System, .Felt252]
                 condition := fun _ (s : Q(System)) _ (a : Q(StorageAddress))
                   _ (s' : Q(System)) (v : Q(F)) =>
                     let m : Q(Metadata) := .fvar metadataRef
                     q(($(s).contracts $(m).contractAddress).storage $a = $v ∧ $s' = $s) },
               { outputTypes := [.GasBuiltin, .System, .Array .Felt252]
                 condition := fun _ (sys : Q(System)) _ _
                   _ (sys' : Q(System)) _ => q($sys' = $sys) }]

def storage_write_syscall : FuncData where
  inputTypes := [.GasBuiltin, .System, .U32, .StorageAddress, .Felt252]
  branches := [{ outputTypes := [.GasBuiltin, .System]
                 condition := fun _ _ _ (a : Q(StorageAddress)) (v : Q(F)) _ (s' : Q(System)) =>
                   let m : Q(Metadata) := .fvar metadataRef
                   -- TODO replace by exact semantics (`s'` is "almost" the same as `s`)
                   q(($(s').contracts $(m).contractAddress).storage $a = $v) },
               { outputTypes := [.GasBuiltin, .System, .Array .Felt252]
                 condition := fun _ (sys : Q(System)) _ _ _ _ (sys' : Q(System)) _ =>
                   q($sys' = $sys) }]

def syscallLibfuncs : Identifier → Option FuncData
| .name "emit_event_syscall" [] .none => emit_event_syscall
| .name "get_execution_info_syscall" [] .none => get_execution_info_syscall
| .name "storage_read_syscall" [] .none => storage_read_syscall metadataRef
| .name "storage_write_syscall" [] .none => storage_write_syscall metadataRef
| _                         => .none
