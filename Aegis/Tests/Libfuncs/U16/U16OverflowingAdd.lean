import Aegis.Tactic

namespace Sierra.Test.U16.U16OverflowingAdd

aegis_load_file "../../e2e_libfuncs/u16_aegis/u16_overflowing_add.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  a.val + b.val < U16_MOD ∧ ρ = .inl (a + b)
  ∨ U16_MOD ≤ a.val + b.val ∧ ρ = .inr (a + b)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  unfold_spec "test::foo"
  rename_i x x_1 x_2
  intro h_auto
  unhygienic cases h_auto
  · simp_all only [and_self, true_or]
  · simp_all only [and_self, or_true]

aegis_complete
