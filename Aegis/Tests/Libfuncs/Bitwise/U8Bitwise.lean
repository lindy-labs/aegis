import Aegis.Commands

namespace Sierra.Test.Bitwise.U8Bitwise

aegis_load_file "../../e2e_libfuncs/bitwise_aegis/u8_bitwise.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  ρ = (a.and b, a.xor b, a.or b)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  rintro rfl
  rfl
