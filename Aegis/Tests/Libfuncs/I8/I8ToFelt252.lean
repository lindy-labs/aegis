import Aegis.Tactic

open Sierra

namespace Sierra.Test.I8.I8ToFelt252

aegis_load_file "../../e2e_libfuncs/i8_aegis/i8_to_felt252.sierra"

aegis_spec "test::foo" :=
  fun _ a ρ =>
  ρ = a.toInt

aegis_prove "test::foo" :=
  fun _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
