import SierraLean.Commands

sierra_load_file "SierraLean/Tests/ternary_add.sierra"

sierra_spec "ternary_add" := fun a b c ρ => ρ = a + b + c

sierra_sound "ternary_add" := fun a b c ρ => by
  rintro ⟨d, _, rfl, rfl, rfl⟩
  unfold spec_ternary_add
  rfl

sierra_load_string "type F = felt252;
 type E = Enum<ut@foo, F, F>;
 libfunc init = enum_init<E, 1>;
 libfunc match = enum_match<E>;
 init([0]) -> ([1]);
 match([1]) { fallthrough([2]) 3([3]) };
 return([2]);
 return([3]);
 foo@0([0]: F) -> (F);"

sierra_spec "foo" := fun a ρ => ρ = a

sierra_sound "foo" := fun a ρ => by
  unfold spec_foo
  rintro ⟨_, _, _, rfl, (⟨h, rfl⟩ | ⟨h, rfl⟩)⟩
  · injection h
  · injection h
