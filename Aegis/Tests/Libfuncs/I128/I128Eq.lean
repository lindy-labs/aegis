import Aegis.Tactic

open Sierra

namespace Sierra.Test.I128.I128Eq

aegis_load_file "../../e2e_libfuncs/i128_aegis/i128_eq.sierra"

aegis_spec "test::foo" :=
  fun _ ρ =>
  ρ = Bool.toSierraBool .false

aegis_prove "test::foo" :=
  fun _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
