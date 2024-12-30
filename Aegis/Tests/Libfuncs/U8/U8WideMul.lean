import Aegis.Tactic

open Sierra

aegis_load_file "../../e2e_libfuncs/u8_aegis/u8_wide_mul.sierra"

aegis_spec "test::foo" :=
  fun _ a b ρ =>
  ρ = a.cast * b.cast

aegis_prove "test::foo" :=
  fun _ a b ρ => by
  unfold_spec "test::foo"
  rename_i x
  intro h_auto
  subst h_auto
  simp_all only

aegis_complete
