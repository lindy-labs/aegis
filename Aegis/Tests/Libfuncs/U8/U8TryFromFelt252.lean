import Aegis.Tactic

namespace Sierra.Test.U8.U8TryFromFelt252

aegis_load_file "../../e2e_libfuncs/u8_aegis/u8_try_from_felt252.sierra"

aegis_spec "test::foo" :=
  fun _ _ a _ ρ =>
  a.val < U8_MOD ∧ ρ = .inl a.val
  ∨ U8_MOD ≤ a.val ∧ ρ = .inr ()

aegis_prove "test::foo" :=
  fun _ _ a _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
