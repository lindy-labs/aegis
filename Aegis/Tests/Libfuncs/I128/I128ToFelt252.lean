import Aegis.Tactic

open Sierra

namespace Sierra.Test.I128.I128ToFelt252

aegis_load_file "../../e2e_libfuncs/i128_aegis/i128_to_felt252.sierra"

aegis_spec "test::foo" :=
  fun _ a ρ =>
  ρ = a.toInt

aegis_prove "test::foo" :=
  fun _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
