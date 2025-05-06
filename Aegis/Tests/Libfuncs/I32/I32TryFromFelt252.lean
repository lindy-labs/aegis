import Aegis.Tactic

open Sierra

namespace Sierra.Test.I32.I32TryFromFelt252

aegis_load_file "../../e2e_libfuncs/i32_aegis/i32_try_from_felt252.sierra"

aegis_spec "test::foo" :=
  fun _ _ a _ ρ =>
  -2^31 ≤ a.valMinAbs ∧ a.valMinAbs < 2^31 ∧ ρ = .inl a.valMinAbs ∨
    (a.valMinAbs < -2^31 ∨ 2^31 ≤ a.valMinAbs) ∧ ρ = .inr ()

aegis_prove "test::foo" :=
  fun _ _ a_ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
