import Aegis.Tactic

open Sierra

aegis_load_file "../../e2e_libfuncs/box_aegis/box_forward_snapshot.sierra"

aegis_spec "test::foo" :=
  fun m a ρ =>
  m.boxHeap (.Snapshot (.Array .Felt252)) ρ
  = m.boxHeap (.Array .Felt252) a

aegis_prove "test::foo" :=
  fun m a ρ => by
  unfold_spec "test::foo"
  intro h_auto
  simp_all only [exists_eq_right]
