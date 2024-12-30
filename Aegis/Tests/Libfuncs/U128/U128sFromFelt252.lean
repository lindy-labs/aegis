import Aegis.Tactic

open Sierra

aegis_load_file "../../e2e_libfuncs/u128_aegis/u128s_from_felt252.sierra"

aegis_spec "test::foo" :=
  fun _ _ a _ ρ =>
  a.val < U128_MOD ∧ ρ = .inl a.cast
  ∨ U128_MOD ≤ a.val ∧ ρ = .inr ((a.val / U128_MOD : UInt128), a.cast)

aegis_prove "test::foo" :=
  fun _ _ a _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
