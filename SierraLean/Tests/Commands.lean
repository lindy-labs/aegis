import SierraLean.Commands

sierra_load_string "type F = felt252; return(); foo@0([0]: F) -> ();"

sierra_load_file "SierraLean/Tests/ternary_add.sierra"

sierra_spec "ternary_add" := fun a b c ρ => ρ = a + b + c

