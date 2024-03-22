import Aegis.Commands

open Sierra

aegis_load_file "../../e2e_libfuncs/array_aegis/array_len.sierra"

aegis_spec "test::foo" :=
  fun _ a ρ₁ ρ₂ =>
  ρ₁ = a ∧ ρ₂ = a.length

aegis_prove "test::foo" :=
  fun _ a ρ₁ ρ₂ => by
  unfold «spec_test::foo»
  rintro ⟨rfl,rfl⟩
  exact ⟨rfl,rfl⟩

aegis_complete
