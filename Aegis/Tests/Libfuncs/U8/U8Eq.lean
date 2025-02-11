import Aegis.Tactic

open Sierra

namespace Sierra.Test.U8.U8Eq

aegis_load_file "../../e2e_libfuncs/u8_aegis/u8_eq.sierra"

aegis_spec "test::foo" :=
  fun _ ρ =>
  ρ = Bool.toSierraBool .false

aegis_prove "test::foo" :=
  fun _ ρ => by
  unfold_spec "test::foo"
  aesop (add simp [BitVec.instIntCast, Int.cast])

aegis_complete
