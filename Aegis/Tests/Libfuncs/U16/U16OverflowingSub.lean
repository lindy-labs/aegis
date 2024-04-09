import Aegis.Commands

open Sierra

aegis_load_file "../../e2e_libfuncs/u16_aegis/u16_overflowing_sub.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  b.val ≤ a.val ∧ ρ = .inl (a - b)
  ∨ a.val < b.val ∧ ρ = .inr (a - b)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  unfold «spec_test::foo»
  rename_i x x_1 x_2
  intro h_auto
  unhygienic aesop_cases h_auto
  · simp_all only [and_self, true_or]
  · simp_all only [and_self, or_true]

aegis_complete
