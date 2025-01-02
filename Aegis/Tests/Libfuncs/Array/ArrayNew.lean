import Aegis.Commands

namespace Sierra.Test.Array.ArrayNew

aegis_load_file "../../e2e_libfuncs/array_aegis/array_new.sierra"

aegis_spec "test::foo" :=
  fun _ ρ =>
  ρ = []

aegis_prove "test::foo" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_complete
