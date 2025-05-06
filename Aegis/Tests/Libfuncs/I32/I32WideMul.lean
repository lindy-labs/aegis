import Aegis.Tactic

open Sierra

namespace Sierra.Test.I32.I32WideMul

aegis_load_file "../../e2e_libfuncs/i32_aegis/i32_wide_mul.sierra"

aegis_spec "test::foo" :=
  fun _ a b ρ =>
  ρ = a.signExtend _ * b.signExtend _

aegis_prove "test::foo" :=
  fun _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
