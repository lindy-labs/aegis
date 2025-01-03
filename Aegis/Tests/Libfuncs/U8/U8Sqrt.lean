import Aegis.Tactic

namespace Sierra.Test.U8.U8Sqrt

aegis_load_file "../../e2e_libfuncs/u8_aegis/u8_sqrt.sierra"

aegis_spec "test::foo" :=
  fun _ _ a _ ρ =>
  ρ = a.toNat.sqrt

aegis_prove "test::foo" :=
  fun _ _ a _ ρ => by
  aesop

aegis_complete
