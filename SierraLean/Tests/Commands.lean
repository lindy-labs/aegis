import SierraLean.Commands

open Sierra

sierra_load_file "SierraLean/Tests/ternary_add.sierra"

sierra_info "ternary_add"

sierra_spec "ternary_add" := fun _ a b c ρ => ρ = a + b + c

sierra_sound "ternary_add" := fun _ a b c ρ => by rintro rfl; rfl

sierra_load_string "type F = felt252;
type E::E::<test>::E = Enum<ut@foo, F, F>;

libfunc init = enum_init<E::E::<test>::E, 1>;
libfunc ematch = enum_match<E::E::<test>::E>;

init([0]) -> ([1]);
ematch([1]) { fallthrough([2]) 3([3]) };
return([2]);
return([3]);

foo@0([0]: F) -> (F);"

sierra_spec "foo" := fun _ a ρ => ρ = a

sierra_sound "foo" := fun _ a ρ => by rintro ⟨_, _, (⟨h, rfl⟩|⟨h, rfl⟩)⟩ <;> injection h

sierra_load_string "type F = felt252;

libfunc c5 = felt252_const<5>;
libfunc call_bar = function_call<user@bar>;

c5() -> ([1]);
return([1]);
call_bar([2]) -> ([3]);
return([3]);

bar@0([0]: F) -> (F);
baz@2([2]: F) -> (F);"

sierra_spec "bar" := fun _ _ ρ => ρ = 5

sierra_sound "bar" := fun _ a ρ => by rintro ⟨rfl⟩; rfl

sierra_spec "baz" := fun _ _ ρ => ρ = 5

sierra_sound "baz" := fun _ a ρ => by rintro ⟨rfl⟩; rfl

sierra_load_string "type F = felt252;

libfunc is_zero = felt252_is_zero;
libfunc call = function_call<user@rec>;
libfunc drop = drop<felt252>;

is_zero([0]) { fallthrough() 2([1]) };
return([0]);
call([0]) -> ([2]);
return([2]);

rec@0([0]: F) -> (F);"

sierra_spec "rec" := fun _ _ ρ => ρ = 0

sierra_sound "rec" := fun _ a ρ => by rintro (⟨rfl, rfl⟩|⟨_, rfl⟩) <;> rfl

sierra_complete

sierra_load_file "SierraLean/Tests/double.sierra"

sierra_spec "double::double::double" := fun _ a ρ => ρ = a * a

sierra_sound "double::double::double" := fun _ a ρ => by
  rintro rfl
  rfl

sierra_load_string "type Unit = Struct<ut@Tuple>;
type core::bool = Enum<ut@core::bool, Unit, Unit>;

libfunc bool_or_impl = bool_or_impl;
libfunc store_temp<core::bool> = store_temp<core::bool>;

bool_or_impl([0], [1]) -> ([2]);
store_temp<core::bool>([2]) -> ([3]);
return([3]);

test::bool_or_impl@0([0]: core::bool, [1]: core::bool) -> (core::bool);"
sierra_spec "test::bool_or_impl" := fun _ _ _ _ => True

sierra_sound "test::bool_or_impl" := fun _ _ _ _ _ => True.intro


sierra_load_string "type Unit = Struct<ut@Tuple>;
type core::bool = Enum<ut@core::bool, Unit, Unit>;

libfunc bool_xor_impl = bool_xor_impl;
libfunc store_temp<core::bool> = store_temp<core::bool>;

bool_xor_impl([0], [1]) -> ([2]);
store_temp<core::bool>([2]) -> ([3]);
return([3]);

test::foo@0([0]: core::bool, [1]: core::bool) -> (core::bool);
test::bar@0([0]: core::bool, [1]: core::bool) -> (core::bool);"

sierra_spec "test::foo" := fun _ a b ρ => (ρ : Bool) = xor a b

sierra_sound "test::foo" := fun _ a b ρ => by
  aesop
