import Aegis.Tactic

namespace Sierra.Test.U32.U32WideMul

aegis_load_file "../../e2e_libfuncs/u32_aegis/u32_wide_mul.sierra"

aegis_spec "test::foo" :=
  fun _ a b ρ =>
  ρ = a.zeroExtend _ * b.zeroExtend _

aegis_prove "test::foo" :=
  fun _ a b ρ => by
  unfold_spec "test::foo"
  intro h
  bv_decide

aegis_complete
