import Aegis.Tactic

namespace Sierra.Test.U16.U16Eq

aegis_load_file "../../e2e_libfuncs/u16_aegis/u16_eq.sierra"

aegis_spec "test::foo" :=
  fun _ ρ =>
  ρ = Bool.toSierraBool .false

aegis_prove "test::foo" :=
  fun _ ρ => by
  unfold_spec "test::foo"
  rintro (⟨-,rfl⟩|⟨h,rfl⟩)
  · simp
  · aesop (add simp [BitVec.instIntCast, Int.cast])

aegis_complete
