import Aegis.Tactic

open Sierra

aegis_load_file "../../e2e_libfuncs/box_aegis/into_box.sierra"

aegis_spec "test::foo" :=
  fun m ρ =>
  m.boxHeap (.Struct []) ρ = .some ()

aegis_prove "test::foo" :=
  fun m ρ => by
  unfold_spec "test::foo"
  intro h_auto
  simp_all only [exists_eq_right]
