import Aegis.Tactic

open Sierra

namespace Test.U8

aegis_load_file "../../e2e_libfuncs/u8_aegis/u8_eq.sierra"

aegis_spec "test::foo" :=
  fun _ ρ =>
  ρ = Bool.toSierraBool .false

aegis_prove "test::foo" :=
  fun _ ρ => by
  unfold_spec "test::foo"
  rintro (⟨-,rfl⟩|⟨h,rfl⟩)
  · simp
  · rw [← sub_eq_zero] at h
    norm_num at h
    letI : Fact (1 < U8_MOD) := ⟨by norm_num [U8_MOD]⟩
    rw [← @ZMod.val_eq_zero, ZMod.val_one U8_MOD] at h
    simp_all

aegis_complete
