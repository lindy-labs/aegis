import Aegis.Tactic

open Sierra

namespace Sierra.Test.I64.I64WideMul

aegis_load_file "../../e2e_libfuncs/i64_aegis/i64_wide_mul.sierra"

aegis_spec "test::foo" :=
  fun _ a b ρ =>
  ρ = a.signExtend _ * b.signExtend _

aegis_prove "test::foo" :=
  fun _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
