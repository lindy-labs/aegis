import Aegis.Commands

open Sierra

aegis_load_file "../../e2e_libfuncs/u16_aegis/u16_try_from_felt252.sierra"

aegis_spec "test::foo" :=
  fun _ _ a _ ρ =>
  a.val < U16_MOD ∧ ρ = .inl a.cast
  ∨ U16_MOD ≤ a.val ∧ ρ = .inr ()

aegis_prove "test::foo" :=
  fun _ _ a _ ρ => by
  unfold «spec_test::foo»
  rename_i x x_1 x_2
  intro h_auto
  unhygienic aesop_cases h_auto
  · simp_all only [and_self, true_or]
  · simp_all only [and_self, or_true]

aegis_complete
