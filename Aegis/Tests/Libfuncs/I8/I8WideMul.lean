import Aegis.Tactic

open Sierra

namespace Sierra.Test.I8.I8WideMul

aegis_load_file "../../e2e_libfuncs/i8_aegis/i8_wide_mul.sierra"

aegis_spec "test::foo" :=
  fun _ a b ρ =>
  ρ = a.signExtend _ * b.signExtend _

aegis_prove "test::foo" :=
  fun _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
