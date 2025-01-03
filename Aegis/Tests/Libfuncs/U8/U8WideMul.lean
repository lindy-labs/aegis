import Aegis.Tactic

namespace Sierra.Test.U8.U8WideMul

aegis_load_file "../../e2e_libfuncs/u8_aegis/u8_wide_mul.sierra"

aegis_spec "test::foo" :=
  fun _ a b ρ =>
  ρ = a.zeroExtend _ * b.zeroExtend _

aegis_prove "test::foo" :=
  fun _ a b ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
