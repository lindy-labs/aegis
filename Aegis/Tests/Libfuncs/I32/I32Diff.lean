import Aegis.Tactic

open Sierra

namespace Sierra.Test.I32.I32Diff

aegis_load_file "../../e2e_libfuncs/i32_aegis/i32_diff.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  b.sle a ∧ ρ = .inl (a - b) ∨
    a.slt b ∧ ρ = .inr (a - b)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
