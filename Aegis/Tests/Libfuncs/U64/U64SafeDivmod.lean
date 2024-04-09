import Aegis.Commands

open Sierra

aegis_load_file "../../e2e_libfuncs/u64_aegis/u64_safe_divmod.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  ρ = (a.ndiv b, a.nmod b)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  unfold «spec_test::foo»
  rename_i x x_1 x_2
  intro h_auto
  aesop_subst h_auto
  simp_all only

aegis_complete
