import Aegis.Tactic

open Sierra

namespace Sierra.Test.I8.I8TryFromFelt252

aegis_load_file "../../e2e_libfuncs/i8_aegis/i8_try_from_felt252.sierra"

aegis_spec "test::foo" :=
  fun _ _ a _ ρ =>
  -2^7 ≤ a.valMinAbs ∧ a.valMinAbs < 2^7 ∧ ρ = .inl a.valMinAbs ∨
    (a.valMinAbs < -2^7 ∨ 2^7 ≤ a.valMinAbs) ∧ ρ = .inr ()

aegis_prove "test::foo" :=
  fun _ _ a_ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
