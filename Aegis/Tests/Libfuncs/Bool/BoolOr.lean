import Aegis.Commands

namespace Sierra.Test.Bool.BoolOr

aegis_load_file "../../e2e_libfuncs/bool_aegis/bool_or.sierra"

aegis_spec "test::foo" :=
  fun _ a b ρ =>
  ρ = Bool.toSierraBool (SierraBool.toBool a || SierraBool.toBool b)

aegis_prove "test::foo" :=
  fun _ a b ρ => by
  rintro rfl
  rfl
