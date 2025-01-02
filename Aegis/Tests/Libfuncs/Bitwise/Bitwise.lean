import Aegis.Commands

namespace Sierra.Test.Bitwise.Bitwise

aegis_load_file "../../e2e_libfuncs/bitwise_aegis/bitwise.sierra"

aegis_spec "test::foo" :=
  fun _ _ a b _ ρ =>
  ρ = ((Nat.land a.val b.val).cast, (Nat.xor a.val b.val).cast, (Nat.lor a.val b.val).cast)

aegis_prove "test::foo" :=
  fun _ _ a b _ ρ => by
  rintro rfl
  rfl
