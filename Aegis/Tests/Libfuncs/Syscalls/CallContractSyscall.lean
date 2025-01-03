import Aegis.Tactic

namespace Sierra.Test.Syscall.CallContractSyscall

aegis_load_file "../../e2e_libfuncs/syscalls_aegis/call_contract_syscall.sierra"

aegis_spec "test::foo" :=
  fun m _ s c f d _ s' ρ =>
  ρ = .inl (m.callResult c f d m.contractAddress s).1
  ∧ s' = (m.callResult c f d m.contractAddress s).2 ∨ ρ.isRight

aegis_prove "test::foo" :=
  fun m _ s c f d _ _ ρ => by
  unfold_spec "test::foo"
  aesop
