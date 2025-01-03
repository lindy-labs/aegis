import Aegis.Tactic

namespace Sierra.Test.U64.U64WideMul

aegis_load_file "../../e2e_libfuncs/u64_aegis/u64_wide_mul.sierra"

aegis_spec "test::foo" :=
  fun _ a b ρ =>
  ρ = a.zeroExtend _ * b.zeroExtend _

aegis_prove "test::foo" :=
  fun _ a b ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
