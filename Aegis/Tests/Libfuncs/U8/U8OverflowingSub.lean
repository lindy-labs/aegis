import Aegis.Tactic

namespace Sierra.Test.U8.U8OverflowingSub

aegis_load_file "../../e2e_libfuncs/u8_aegis/u8_overflowing_sub.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  ¬ BitVec.usubOverflow a b ∧ ρ = .inl (a - b)
    ∨ BitVec.usubOverflow a b ∧ ρ = .inr (a - b)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
