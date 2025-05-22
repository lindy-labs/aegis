import Aegis.Tactic

open Sierra

namespace Sierra.Test.Bytes31.Bytes31ToFelt252

aegis_load_file "../../e2e_libfuncs/bytes31_aegis/bytes31_to_felt252.sierra"

aegis_spec "test::foo" :=
  fun _ a ρ =>
  ρ = Fin.castLE (m := PRIME) (by simp [PRIME]) a.toFin

aegis_prove "test::foo" :=
  fun _ a ρ => by
  rintro rfl
  rfl
