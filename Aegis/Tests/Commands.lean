import Aegis.Commands

open Sierra

aegis_load_file "Aegis/Tests/ternary_add.sierra"

aegis_info "ternary_add"

aegis_spec "ternary_add" := fun _ a b c ρ => ρ = a + b + c

aegis_prove "ternary_add" := fun _ a b c ρ => by rintro rfl; rfl

aegis_load_string "type F = felt252;
type E::E::<test>::E = Enum<ut@foo, F, F>;

libfunc init = enum_init<E::E::<test>::E, 1>;
libfunc ematch = enum_match<E::E::<test>::E>;

init([0]) -> ([1]);
ematch([1]) { fallthrough([2]) 3([3]) };
return([2]);
return([3]);

foo@0([0]: F) -> (F);"

aegis_spec "foo" := fun _ a ρ => ρ = a

aegis_prove "foo" := fun _ a ρ => by rintro ⟨_, _, (⟨h, rfl⟩|⟨h, rfl⟩)⟩ <;> injection h

aegis_load_string "type F = felt252;

libfunc c5 = felt252_const<5>;
libfunc call_bar = function_call<user@bar>;

c5() -> ([1]);
return([1]);
call_bar([2]) -> ([3]);
return([3]);

bar@0([0]: F) -> (F);
baz@2([2]: F) -> (F);"

aegis_spec "bar" := fun _ _ ρ => ρ = 5

aegis_prove "bar" := fun _ a ρ => by rintro ⟨rfl⟩; rfl

aegis_spec "baz" := fun _ _ ρ => ρ = 5

aegis_prove "baz" := fun _ a ρ => by rintro ⟨rfl⟩; rfl

aegis_load_string "type F = felt252;

libfunc is_zero = felt252_is_zero;
libfunc call = function_call<user@rec>;
libfunc drop = drop<felt252>;

is_zero([0]) { fallthrough() 2([1]) };
return([0]);
call([0]) -> ([2]);
return([2]);

rec@0([0]: F) -> (F);"

aegis_spec "rec" := fun _ _ ρ => ρ = 0

aegis_prove "rec" := fun _ a ρ => by rintro (⟨rfl, rfl⟩|⟨_, rfl⟩) <;> rfl

aegis_complete

aegis_load_file "Aegis/Tests/double.sierra"

aegis_spec "double::double::double" := fun _ a ρ => ρ = a * a

aegis_prove "double::double::double" := fun _ a ρ => by
  rintro rfl
  rfl

aegis_load_string "type Unit = Struct<ut@Tuple>;
type core::bool = Enum<ut@core::bool, Unit, Unit>;

libfunc bool_or_impl = bool_or_impl;
libfunc store_temp<core::bool> = store_temp<core::bool>;

bool_or_impl([0], [1]) -> ([2]);
store_temp<core::bool>([2]) -> ([3]);
return([3]);

test::bool_or_impl@0([0]: core::bool, [1]: core::bool) -> (core::bool);"
aegis_spec "test::bool_or_impl" := fun _ _ _ _ => True

aegis_prove "test::bool_or_impl" := fun _ _ _ _ _ => True.intro

aegis_load_string "type u128 = u128;
type Unit = Struct<ut@Tuple>;
type core::bool = Enum<ut@core::bool, Unit, Unit>;

libfunc u128_const<11> = u128_const<11>;
libfunc u128_const<12> = u128_const<12>;
libfunc store_temp<u128> = store_temp<u128>;
libfunc u128_eq = u128_eq;
libfunc branch_align = branch_align;
libfunc struct_construct<Unit> = struct_construct<Unit>;
libfunc enum_init<core::bool, 0> = enum_init<core::bool, 0>;
libfunc store_temp<core::bool> = store_temp<core::bool>;
libfunc jump = jump;
libfunc enum_init<core::bool, 1> = enum_init<core::bool, 1>;
libfunc rename<core::bool> = rename<core::bool>;

u128_const<11>() -> ([0]);
u128_const<12>() -> ([1]);
store_temp<u128>([0]) -> ([0]);
u128_eq([0], [1]) { fallthrough() 9() };
branch_align() -> ();
struct_construct<Unit>() -> ([2]);
enum_init<core::bool, 0>([2]) -> ([3]);
store_temp<core::bool>([3]) -> ([4]);
jump() { 13() };
branch_align() -> ();
struct_construct<Unit>() -> ([5]);
enum_init<core::bool, 1>([5]) -> ([6]);
store_temp<core::bool>([6]) -> ([4]);
rename<core::bool>([4]) -> ([7]);
return([7]);

test::u128_const@0() -> (core::bool);"

aegis_spec "test::u128_const" := fun _ _ => True

aegis_prove "test::u128_const" := fun _ _ _ => True.intro

aegis_load_string "type Unit = Struct<ut@Tuple>;
type core::bool = Enum<ut@core::bool, Unit, Unit>;

libfunc bool_xor_impl = bool_xor_impl;
libfunc store_temp<core::bool> = store_temp<core::bool>;

bool_xor_impl([0], [1]) -> ([2]);
store_temp<core::bool>([2]) -> ([3]);
return([3]);

test::foo@0([0]: core::bool, [1]: core::bool) -> (core::bool);
test::bar@0([0]: core::bool, [1]: core::bool) -> (core::bool);"

aegis_spec "test::foo" := fun _ a b ρ => (ρ : Bool) = xor a b

set_option aegis.contract false
set_option aegis.filterUnused false
set_option aegis.normalize false
aegis_prove "test::foo" := fun _ a b ρ => by
  unfold Bool.toSierraBool
  unfold «spec_test::foo»
  aesop
