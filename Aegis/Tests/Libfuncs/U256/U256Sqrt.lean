import Aegis.Tactic

namespace Sierra.Test.U256.U256Sqrt

aegis_load_file "../../e2e_libfuncs/u256_aegis/u256_sqrt.sierra"

aegis_spec "test::foo" :=
  fun _ _ a _ ρ =>
  ρ = (a.2.append a.1).toNat.sqrt

aegis_prove "test::foo" :=
  fun _ _ a _ ρ => by
  aesop
