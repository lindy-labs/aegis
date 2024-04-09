import Aegis.Commands

open Sierra

aegis_load_file "../../e2e_libfuncs/u32_aegis/u32_wide_mul.sierra"

aegis_spec "test::foo" :=
  fun _ a b ρ =>
  ρ = a.cast * b.cast

aegis_prove "test::foo" :=
  fun _ a b ρ => by
  unfold «spec_test::foo»
  rename_i x
  intro h_auto
  aesop_subst h_auto
  simp_all only

aegis_complete
