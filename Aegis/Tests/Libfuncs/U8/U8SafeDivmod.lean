import Aegis.Tactic

namespace Sierra.Test.U8.U8SafeDivmod

aegis_load_file "../../e2e_libfuncs/u8_aegis/u8_safe_divmod.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  ρ = (a / b, a % b)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  aesop

aegis_complete
