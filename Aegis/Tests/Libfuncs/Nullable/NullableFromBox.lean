import Aegis.Commands

open Sierra

aegis_load_file "../../e2e_libfuncs/nullable_aegis/nullable_from_box.sierra"

aegis_spec "test::foo" :=
  fun m a ρ =>
  ρ = m.boxHeap .Felt252 a

aegis_prove "test::foo" :=
  fun m a ρ => by
  rintro rfl
  rfl

aegis_complete
