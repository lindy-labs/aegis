import Aegis.Tactic

open Sierra

namespace Sierra.Test.I64.I64Eq

aegis_load_file "../../e2e_libfuncs/i64_aegis/i64_eq.sierra"

aegis_spec "test::foo" :=
  fun _ ρ =>
  ρ = Bool.toSierraBool .false

aegis_prove "test::foo" :=
  fun _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
