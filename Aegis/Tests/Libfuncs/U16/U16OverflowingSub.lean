import Aegis.Tactic

namespace Sierra.Test.U16.U16OverflowingSub

aegis_load_file "../../e2e_libfuncs/u16_aegis/u16_overflowing_sub.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  b ≤ a ∧ ρ = .inl (a - b)
  ∨ a < b ∧ ρ = .inr (a - b)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
