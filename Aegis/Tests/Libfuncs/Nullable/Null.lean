import Aegis.Commands

open Sierra

aegis_load_file "../../e2e_libfuncs/nullable_aegis/null.sierra"

aegis_spec "test::foo" :=
  fun _ ρ =>
  ρ = .none

aegis_prove "test::foo" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_complete
