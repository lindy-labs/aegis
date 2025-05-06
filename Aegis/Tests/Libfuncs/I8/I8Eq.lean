import Aegis.Tactic

open Sierra

namespace Sierra.Test.I8.I8Eq

aegis_load_file "../../e2e_libfuncs/i8_aegis/i8_eq.sierra"

aegis_spec "test::foo" :=
  fun _ ρ =>
  ρ = Bool.toSierraBool .false

aegis_prove "test::foo" :=
  fun _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
