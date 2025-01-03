import Aegis.Tactic

namespace Sierra.Test.U64.U64Eq

aegis_load_file "../../e2e_libfuncs/u64_aegis/u64_eq.sierra"

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
