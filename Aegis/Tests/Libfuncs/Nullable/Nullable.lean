import Aegis.Commands

open Sierra

aegis_load_file "../../e2e_libfuncs/nullable_aegis/nullable.sierra"

aegis_spec "test::foo" :=
 fun _ ρ =>
 ρ = 1

aegis_prove "test::foo" :=
  fun _ ρ => by
  unfold «spec_test::foo»
  rintro ⟨_,_,h₁,(⟨h₂,-⟩|⟨-,-,rfl⟩)⟩
  · simp_all only
  · simp

aegis_complete
