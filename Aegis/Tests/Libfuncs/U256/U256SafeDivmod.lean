import Aegis.Tactic

namespace Sierra.Test.U256.U256SafeDivmod

aegis_load_file "../../e2e_libfuncs/u256_aegis/u256_safe_divmod.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  ρ.1.2 ++ ρ.1.1 = (a.2 ++ a.1) / (b.2 ++ b.1)
  ∧ ρ.2.2 ++ ρ.2.1 = (a.2 ++ a.1) % (b.2 ++ b.1)

set_option aegis.separateTuples true in
aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  unfold_spec "test::foo"
  aesop
