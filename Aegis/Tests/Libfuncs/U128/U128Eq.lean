import Aegis.Tactic

open Sierra

aegis_load_file "../../e2e_libfuncs/u128_aegis/u128_eq.sierra"

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
    letI : Fact (1 < U128_MOD) := ⟨by norm_num [U128_MOD]⟩
    rw [← @ZMod.val_eq_zero, ZMod.val_one U128_MOD] at h
    simp_all

aegis_complete
