import Aegis.Tactic

open Sierra

namespace Sierra.Test.I64.I64TryFromFelt252

aegis_load_file "../../e2e_libfuncs/i64_aegis/i64_try_from_felt252.sierra"

aegis_spec "test::foo" :=
  fun _ _ a _ ρ =>
  -2^63 ≤ a.valMinAbs ∧ a.valMinAbs < 2^63 ∧ ρ = .inl a.valMinAbs ∨
    (a.valMinAbs < -2^63 ∨ 2^63 ≤ a.valMinAbs) ∧ ρ = .inr ()

aegis_prove "test::foo" :=
  fun _ _ a_ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
