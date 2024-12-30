import Aegis.Tactic

open Sierra

aegis_load_file "../../e2e_libfuncs/u16_aegis/u16_safe_divmod.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  ρ = (a.ndiv b, a.nmod b)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  unfold_spec "test::foo"
  rename_i x x_1 x_2
  intro h_auto
  subst h_auto
  simp_all only

aegis_complete
