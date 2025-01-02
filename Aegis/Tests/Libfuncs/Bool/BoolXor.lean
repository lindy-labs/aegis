import Aegis.Commands

namespace Sierra.Test.Bool.BoolXor

aegis_load_file "../../e2e_libfuncs/bool_aegis/bool_xor.sierra"

aegis_spec "test::foo" :=
  fun _ a b ρ =>
  ρ = Bool.toSierraBool (xor (SierraBool.toBool a) (SierraBool.toBool b))

aegis_prove "test::foo" :=
  fun _ a b ρ => by
  rintro rfl
  rfl
