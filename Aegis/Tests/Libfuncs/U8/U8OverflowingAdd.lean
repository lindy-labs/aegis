import Aegis.Tactic

namespace Sierra.Test.U8.U8Overflowingadd

aegis_load_file "../../e2e_libfuncs/u8_aegis/u8_overflowing_add.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  a.toNat + b.toNat < U8_MOD ∧ ρ = .inl (a + b)
  ∨ U8_MOD ≤ a.toNat + b.toNat ∧ ρ = .inr (a + b)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  unfold_spec "test::foo"
  rename_i x x_1 x_2
  intro h_auto
  unhygienic cases h_auto
  · simp_all only [and_self, true_or]
  · simp_all only [and_self, or_true]

aegis_complete
