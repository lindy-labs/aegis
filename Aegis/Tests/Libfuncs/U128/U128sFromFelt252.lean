import Aegis.Commands

open Sierra

aegis_load_file "../../e2e_libfuncs/u128_aegis/u128s_from_felt252.sierra"

aegis_spec "test::foo" :=
  fun _ _ a _ ρ =>
  a.val < U128_MOD ∧ ρ = .inl a.cast
  ∨ U128_MOD ≤ a.val ∧ ρ = .inr ((a.val % U128_MOD : UInt128), a.cast)

aegis_prove "test::foo" :=
  fun _ _ a _ ρ => by
  unfold «spec_test::foo»
  rename_i x x_1 x_2
  intro h_auto
  simp_all only [ZMod.nat_cast_mod]
  unhygienic aesop_cases h_auto
  · simp_all only [and_self, true_or]
  · simp_all only [and_self, or_true]

aegis_complete
