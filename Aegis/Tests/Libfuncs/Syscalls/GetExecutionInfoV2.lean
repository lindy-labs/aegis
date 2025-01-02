import Aegis.Tactic

namespace Sierra.Test.Syscalls.GetExecutionInfoV2

aegis_load_file "../../e2e_libfuncs/syscalls_aegis/get_execution_info_v2_syscall.sierra"

aegis_spec "test::foo" :=
  fun m _ s _ s' ρ =>
  s' = s ∧
  ((∃ rei rbi rti, ρ = .inl rei ∧
    m.boxHeap .V2ExecutionInfo rei = .some ⟨rbi, rti,
      m.callerAddress, m.contractAddress, m.entryPointSelector⟩
    ∧ m.boxHeap .BlockInfo rbi = .some ⟨m.blockNumber, m.blockTimestamp, m.sequencerAddress⟩
    ∧ m.boxHeap .V2TxInfo rti = .some ⟨m.txVersion, m.txContract, m.txMaxFee, m.txSignature,
      m.txHash, m.txChainIdentifier, m.txNonce, m.txResourceBounds, m.txTip, m.txPaymasterData,
      m.txDataAvailabilityNonce, m.txDataAvailabilityFee, m.txAccountDeploymentData⟩)
  ∨ ρ.isRight)

aegis_prove "test::foo" :=
  fun m _ s _ s' ρ => by
  unfold_spec "test::foo"
  rintro ⟨rei,_,(⟨h,rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · rcases h with ⟨ρ',rbi,bi,rti,ti,h₁,h₂,h₃,rfl,rfl,rfl⟩
    refine ⟨rfl, .inl ?_⟩
    use rei; use rbi; use rti
  · exact ⟨rfl, .inr Sum.isRight_inr⟩
