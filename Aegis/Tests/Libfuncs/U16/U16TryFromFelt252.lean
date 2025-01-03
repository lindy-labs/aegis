import Aegis.Tactic

namespace Sierra.Test.U16.U16TryFromFelt252

aegis_load_file "../../e2e_libfuncs/u16_aegis/u16_try_from_felt252.sierra"

aegis_spec "test::foo" :=
  fun _ _ a _ ρ =>
  a.val < U16_MOD ∧ ρ = .inl a.val
  ∨ U16_MOD ≤ a.val ∧ ρ = .inr ()

aegis_prove "test::foo" :=
  fun _ _ a _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
