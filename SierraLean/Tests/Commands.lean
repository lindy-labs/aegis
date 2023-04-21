import SierraLean.Commands

namespace Sierra

sierra_load_file "SierraLean/Tests/ternary_add.sierra"

sierra_spec "ternary_add" := fun a b c ρ => ρ = a + b + c

sierra_sound "ternary_add" := _
