import Aegis.Tactic

open Sierra

aegis_load_file "../../e2e_libfuncs/u32_aegis/u32_eq.sierra"

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
    letI : Fact (1 < U32_MOD) := ⟨by norm_num [U32_MOD]⟩
    rw [← @ZMod.val_eq_zero, ZMod.val_one U32_MOD] at h
    simp_all

aegis_complete
