import SierraLean.Commands

sierra_load_file "SierraLean/Tests/ternary_add.sierra"

sierra_spec "ternary_add" := fun a b c ρ => ρ = a + b + c

sierra_sound "ternary_add" := fun a b c ρ => by
  rintro ⟨d, _, rfl, rfl, rfl⟩
  unfold spec_ternary_add
  rfl
