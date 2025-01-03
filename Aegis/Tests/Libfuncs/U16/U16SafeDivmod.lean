import Aegis.Tactic

namespace Sierra.Test.U16.U16SafeDivmod

aegis_load_file "../../e2e_libfuncs/u16_aegis/u16_safe_divmod.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  ρ = (a / b, a % b)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
