import Aegis.Tactic

open Sierra

aegis_load_file "../../e2e_libfuncs/storage_address_aegis/storage_base_address_from_felt252.sierra"

aegis_spec "test::foo" :=
  fun _ _ a _ ρ =>
  ρ = a.cast

aegis_prove "test::foo" :=
  fun _ _ a _ ρ => by
  unfold_spec "test::foo"
  rename_i x x_1 x_2
  intro h_auto
  subst h_auto
  simp_all only

aegis_complete
