import Aegis.Tactic

namespace Sierra.Test.U128.U128OverflowingSub

aegis_load_file "../../e2e_libfuncs/u128_aegis/u128_overflowing_sub.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  b.val ≤ a.val ∧ ρ = .inl (a - b)
  ∨ a.val < b.val ∧ ρ = .inr (a - b)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  unfold_spec "test::foo"
  rename_i x x_1 x_2
  intro h_auto
  cases h_auto
  · simp_all only [and_self, true_or]
  · simp_all only [and_self, or_true]

aegis_complete
