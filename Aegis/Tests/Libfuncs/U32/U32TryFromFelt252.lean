import Aegis.Tactic

namespace Sierra.Test.U32.U32TryFromFelt252

aegis_load_file "../../e2e_libfuncs/u32_aegis/u32_try_from_felt252.sierra"

aegis_spec "test::foo" :=
  fun _ _ a _ ρ =>
  a.val < U32_MOD ∧ ρ = .inl a.val
  ∨ U32_MOD ≤ a.val ∧ ρ = .inr ()

aegis_prove "test::foo" :=
  fun _ _ a _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
