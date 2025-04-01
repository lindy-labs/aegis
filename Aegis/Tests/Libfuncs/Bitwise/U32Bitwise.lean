import Aegis.Tactic

namespace Sierra.Test.Bitwise.U32Bitwise

aegis_load_file "../../e2e_libfuncs/bitwise_aegis/u32_bitwise.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  ρ = (a.and b, a.xor b, a.or b)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  rintro rfl
  unfold_spec "test::foo"
  rfl
