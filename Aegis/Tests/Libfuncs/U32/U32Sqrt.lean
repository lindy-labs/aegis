import Aegis.Tactic

namespace Sierra.Test.U32.U32Sqrt

aegis_load_file "../../e2e_libfuncs/u32_aegis/u32_sqrt.sierra"

aegis_spec "test::foo" :=
  fun _ _ a _ ρ =>
  ρ = a.toNat.sqrt

aegis_prove "test::foo" :=
  fun _ _ a _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
