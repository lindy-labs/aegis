import Aegis.Commands

open Sierra

aegis_load_file "../../e2e_libfuncs/u32_aegis/u32_sqrt.sierra"

aegis_spec "test::foo" :=
  fun _ _ a _ ρ =>
  ρ.val = a.val.sqrt

aegis_prove "test::foo" :=
  fun _ _ a _ ρ => by
  unfold «spec_test::foo»
  rename_i x x_1 x_2
  intro h_auto
  simp_all only [exists_eq_right]

aegis_complete
