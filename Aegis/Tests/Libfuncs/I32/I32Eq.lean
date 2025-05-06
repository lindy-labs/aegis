import Aegis.Tactic

open Sierra

namespace Sierra.Test.I32.I32Eq

aegis_load_file "../../e2e_libfuncs/i32_aegis/i32_eq.sierra"

aegis_spec "test::foo" :=
  fun _ ρ =>
  ρ = Bool.toSierraBool .false

aegis_prove "test::foo" :=
  fun _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
