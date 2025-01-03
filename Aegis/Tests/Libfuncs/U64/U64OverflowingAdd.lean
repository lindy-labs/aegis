import Aegis.Tactic

namespace Sierra.Test.U64.U64Overflowingadd

aegis_load_file "../../e2e_libfuncs/u64_aegis/u64_overflowing_add.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  a.toNat + b.toNat < U64_MOD ∧ ρ = .inl (a + b)
  ∨ U64_MOD ≤ a.toNat + b.toNat ∧ ρ = .inr (a + b)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
