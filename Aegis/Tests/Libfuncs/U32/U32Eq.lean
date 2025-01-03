import Aegis.Tactic

namespace Sierra.Test.U32.U32Eq

aegis_load_file "../../e2e_libfuncs/u32_aegis/u32_eq.sierra"

aegis_spec "test::foo" :=
  fun _ ρ =>
  ρ = Bool.toSierraBool .false

aegis_prove "test::foo" :=
  fun _ ρ => by
  unfold_spec "test::foo"
  rintro (⟨-,rfl⟩|⟨h,rfl⟩)
  · simp
  · aesop (add simp [Int.cast, BitVec.instIntCast])

aegis_complete
