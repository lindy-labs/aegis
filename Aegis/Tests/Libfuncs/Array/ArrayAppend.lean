import Aegis.Commands

open Sierra

aegis_load_file "../../e2e_libfuncs/array_aegis/array_append.sierra"

aegis_spec "test::foo" :=
  fun _ a b c ρ _ =>
  ρ = a ++ [b] ++ [c]

aegis_prove "test::foo" :=
  fun _ a b c ρ _ => by
  unfold «spec_test::foo»
  rintro ⟨rfl,rfl⟩
  rfl

aegis_complete
