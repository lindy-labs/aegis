import Aegis.Tactic

namespace Sierra.Test.U16.U16WideMul

aegis_load_file "../../e2e_libfuncs/u16_aegis/u16_wide_mul.sierra"

aegis_spec "test::foo" :=
  fun _ a b ρ =>
  ρ = a.zeroExtend _ * b.zeroExtend _

aegis_prove "test::foo" :=
  fun _ a b ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
