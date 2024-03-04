import Aegis.Types
import Mathlib.Data.ZMod.Basic

open Qq Sierra Lean

namespace Sierra.FuncData

variable (metadataRef : FVarId)

def emit_event_syscall : FuncData where
  inputTypes := [.GasBuiltin, .System, .Snapshot (.Array .Felt252), .Snapshot (.Array .Felt252)]
  branches := [{ outputTypes := [.GasBuiltin, .System]
                 condition := fun _ (s : Q(System)) (k : Q(List F)) (d : Q(List F))
                   _ (s' : Q(System)) =>
                     let m : Q(Metadata) := .fvar metadataRef
                     q($s' = $(s).emitEvent { contract := $(m).contractAddress
                                              keys := $k
                                              data := $d }) },
               { outputTypes := [.GasBuiltin, .System, .Array .Felt252]
                 condition := fun _ (s : Q(System)) _ _ _ (s' : Q(System)) _ => q($s' = $s) }]

open Sierra

def get_execution_info_syscall : FuncData where
  inputTypes := [.GasBuiltin, .System]
  branches := [{ outputTypes := [.GasBuiltin, .System, .Box <| .ExecutionInfo]
                 condition := fun _ (sys : Q(System)) _ (sys' : Q(System))
                     (ρ: Q(Nat)) =>
                     let m : Q(Metadata) := .fvar metadataRef
                     q($sys' = $sys ∧
                       ∃ ρ' rbi bi rti ti, $(m).boxHeap .ExecutionInfo $ρ = .some ρ'
                         ∧ $(m).boxHeap .BlockInfo rbi = .some bi
                         ∧ $(m).boxHeap .TxInfo rti = .some ti
                         ∧ bi = ⟨$(m).blockNumber, $(m).blockTimestamp, $(m).sequencerAddress⟩
                         ∧ ti = ⟨$(m).txVersion, $(m).txContract, $(m).txMaxFee, $(m).txSignature,
                             $(m).txHash, $(m).txChainIdentifier, $(m).txNonce⟩
                         ∧ ρ' = ⟨rbi, rti,
                           $(m).callerAddress, $(m).contractAddress, $(m).entryPointSelector⟩) },
               { outputTypes := [.GasBuiltin, .System, .Array .Felt252]
                 condition := fun _ (sys : Q(System)) _ (sys' : Q(System)) _ =>
                   q($sys' = $sys) }]

def storage_read_syscall : FuncData where
  inputTypes := [.GasBuiltin, .System, .U32, .StorageAddress]
  branches := [{ outputTypes := [.GasBuiltin, .System, .Felt252]
                 condition := fun _ (s : Q(System)) _ (a : Q(StorageAddress))
                   _ (s' : Q(System)) (v : Q(F)) =>
                     let m : Q(Metadata) := .fvar metadataRef
                     let ca : Q(F) := q($(m).contractAddress.cast)
                     q(($(s).contracts $ca).storage $a = $v ∧ $s' = $s) },
               { outputTypes := [.GasBuiltin, .System, .Array .Felt252]
                 condition := fun _ (sys : Q(System)) _ _
                   _ (sys' : Q(System)) _ => q($sys' = $sys) }]

def storage_write_syscall : FuncData where
  inputTypes := [.GasBuiltin, .System, .U32, .StorageAddress, .Felt252]
  branches := [{ outputTypes := [.GasBuiltin, .System]
                 condition := fun _ (s : Q(System)) _ (a : Q(StorageAddress)) (v : Q(F))
                   _ (s' : Q(System)) =>
                     let m : Q(Metadata) := .fvar metadataRef
                     let ca : Q(F) := q($(m).contractAddress.cast)
                     q($s' = ($s).writeStorage $ca $a $v) },
               { outputTypes := [.GasBuiltin, .System, .Array .Felt252]
                 condition := fun _ (sys : Q(System)) _ _ _ _ (sys' : Q(System)) _ =>
                   q($sys' = $sys) }]

def call_contract_syscall : FuncData where
  inputTypes := [.GasBuiltin, .System, .ContractAddress, .Felt252, .Array .Felt252]
  branches := [{ outputTypes := [.GasBuiltin, .System, .Array .Felt252]
                 condition := fun _ (s : Q(System)) (c : Q(ContractAddress))
                   (f : Q(F)) (d : Q(List F)) _ (s' : Q(System)) (r : Q(List F)) =>
                     let m : Q(Metadata) := .fvar metadataRef
                     q($r = (($m).callResult $c $f $d $(m).contractAddress $s).fst
                       ∧ $s' = (($m).callResult $c $f $d $(m).contractAddress $s).snd) },
               { outputTypes := [.GasBuiltin, .System, .Array .Felt252]
                 condition := fun _ _ _ _ _
                   _ _ _ => q(True) }]  -- TODO can we assume that `s' = s`?

def syscallLibfuncs : Identifier → Option FuncData
| .name "emit_event_syscall" [] .none => emit_event_syscall metadataRef
| .name "get_execution_info_syscall" [] .none => get_execution_info_syscall metadataRef
| .name "storage_read_syscall" [] .none => storage_read_syscall metadataRef
| .name "storage_write_syscall" [] .none => storage_write_syscall metadataRef
| .name "call_contract_syscall" [] .none => call_contract_syscall metadataRef
| _                         => .none
