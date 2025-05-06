import Aegis.Tactic

open Sierra

namespace Sierra.Test.I16.I16Eq

aegis_load_file "../../e2e_libfuncs/i16_aegis/i16_eq.sierra"

aegis_spec "test::foo" :=
  fun _ ρ =>
  ρ = Bool.toSierraBool .false

aegis_prove "test::foo" :=
  fun _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
