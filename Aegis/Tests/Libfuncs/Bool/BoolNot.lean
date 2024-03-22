import Aegis.Commands

open Sierra

aegis_load_file "../../e2e_libfuncs/bool_aegis/bool_not.sierra"

aegis_spec "test::foo" :=
  fun _ a ρ =>
  ρ = Bool.toSierraBool (!SierraBool.toBool a)

aegis_prove "test::foo" :=
  fun _ a ρ => by
  rintro rfl
  rfl
