import Aegis.Tactic

open Sierra

aegis_load_file "../../e2e_libfuncs/u64_aegis/u64_overflowing_sub.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  b ≤ a ∧ ρ = .inl (a - b)
  ∨ a < b ∧ ρ = .inr (a - b)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
