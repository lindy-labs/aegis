import Aegis.Tactic

open Sierra

aegis_load_file "../../e2e_libfuncs/u32_aegis/u32_is_zero.sierra"

aegis_spec "test::foo" :=
  fun _ a ρ =>
  ρ =  if a = 0 then 1234 else a

aegis_prove "test::foo" :=
  fun _ a ρ => by
  unfold_spec "test::foo"
  rintro (⟨rfl,rfl⟩|⟨h,rfl⟩)
  · simp
  · simp [h]

aegis_complete
