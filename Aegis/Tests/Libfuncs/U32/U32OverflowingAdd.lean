import Aegis.Tactic

namespace Sierra.Test.U32.U32OverflowingAdd

aegis_load_file "../../e2e_libfuncs/u32_aegis/u32_overflowing_add.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  a.toNat + b.toNat < U32_MOD ∧ ρ = .inl (a + b)
  ∨ U32_MOD ≤ a.toNat + b.toNat ∧ ρ = .inr (a + b)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
