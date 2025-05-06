import Aegis.Tactic

open Sierra

namespace Sierra.Test.I64.I64Diff

aegis_load_file "../../e2e_libfuncs/i64_aegis/i64_diff.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  b.sle a ∧ ρ = .inl (a - b) ∨
    a.slt b ∧ ρ = .inr (a - b)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
