import Aegis.Tactic

namespace Sierra.Test.U64.U64SafeDivmod

aegis_load_file "../../e2e_libfuncs/u64_aegis/u64_safe_divmod.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  ρ = (a / b, a % b)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
