import Aegis.Tactic

namespace Sierra.Test.U128.U128Overflowingadd

aegis_load_file "../../e2e_libfuncs/u128_aegis/u128_overflowing_add.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  a.toNat + b.toNat < U128_MOD ∧ ρ = .inl (a + b)
  ∨ U128_MOD ≤ a.toNat + b.toNat ∧ ρ = .inr (a + b)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  unfold «spec_test::foo»
  aesop

aegis_complete
