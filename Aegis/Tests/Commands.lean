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

aegis_load_string "type felt252 = felt252 [storable: true, drop: true, dup: true, zero_sized: false];
type Box<felt252> = Box<felt252> [storable: true, drop: true, dup: true, zero_sized: false];

libfunc into_box<felt252> = into_box<felt252>;

into_box<felt252>([0]) -> ([1]); // 0
return([1]); // 1

test::into_box@0([0]: felt252) -> (Box<felt252>);"

aegis_spec "test::into_box" := fun m a ρ =>
  m.boxHeap .Felt252 ρ = .some a

aegis_prove "test::into_box" := fun _ _ _ _ => by
  aesop

aegis_load_string "type Box<felt252> = Box<felt252> [storable: true, drop: true, dup: true, zero_sized: false];
type felt252 = felt252 [storable: true, drop: true, dup: true, zero_sized: false];

libfunc unbox<felt252> = unbox<felt252>;
libfunc store_temp<felt252> = store_temp<felt252>;

unbox<felt252>([0]) -> ([1]); // 0
store_temp<felt252>([1]) -> ([1]); // 1
return([1]); // 2

test::unbox@0([0]: Box<felt252>) -> (felt252);"

aegis_spec "test::unbox" := fun m a ρ =>
  m.boxHeap .Felt252 a = .some ρ

aegis_prove "test::unbox" := fun m a b => by
  unfold «spec_test::unbox»
  rintro ⟨_,h,rfl⟩
  symm
  assumption

aegis_load_string "type RangeCheck = RangeCheck [storable: true, drop: false, dup: false, zero_sized: false];
type u128 = u128 [storable: true, drop: true, dup: true, zero_sized: false];
type core::integer::u256 = Struct<ut@core::integer::u256, u128, u128> [storable: true, drop: true, dup: true, zero_sized: false];
type Tuple<core::integer::u256, core::integer::u256> = Struct<ut@Tuple, core::integer::u256, core::integer::u256> [storable: true, drop: true, dup: true, zero_sized: false];
type Unit = Struct<ut@Tuple> [storable: true, drop: true, dup: true, zero_sized: true];
type U128MulGuarantee = U128MulGuarantee [storable: true, drop: false, dup: false, zero_sized: false];
type NonZero<core::integer::u256> = NonZero<core::integer::u256> [storable: true, drop: true, dup: true, zero_sized: false];

libfunc u256_safe_divmod = u256_safe_divmod;
libfunc store_temp<RangeCheck> = store_temp<RangeCheck>;
libfunc store_temp<U128MulGuarantee> = store_temp<U128MulGuarantee>;
libfunc function_call<user@core::integer::U128MulGuaranteeDestruct::destruct> = function_call<user@core::integer::U128MulGuaranteeDestruct::destruct>;
libfunc drop<Unit> = drop<Unit>;
libfunc struct_construct<Tuple<core::integer::u256, core::integer::u256>> = struct_construct<Tuple<core::integer::u256, core::integer::u256>>;
libfunc store_temp<Tuple<core::integer::u256, core::integer::u256>> = store_temp<Tuple<core::integer::u256, core::integer::u256>>;
libfunc u128_mul_guarantee_verify = u128_mul_guarantee_verify;
libfunc struct_construct<Unit> = struct_construct<Unit>;
libfunc store_temp<Unit> = store_temp<Unit>;

u256_safe_divmod([0], [1], [2]) -> ([3], [4], [5], [6]); // 0
store_temp<RangeCheck>([3]) -> ([3]); // 1
store_temp<U128MulGuarantee>([6]) -> ([6]); // 2
function_call<user@core::integer::U128MulGuaranteeDestruct::destruct>([3], [6]) -> ([7], [8]); // 3
drop<Unit>([8]) -> (); // 4
struct_construct<Tuple<core::integer::u256, core::integer::u256>>([4], [5]) -> ([9]); // 5
store_temp<RangeCheck>([7]) -> ([7]); // 6
store_temp<Tuple<core::integer::u256, core::integer::u256>>([9]) -> ([9]); // 7
return([7], [9]); // 8
u128_mul_guarantee_verify([0], [1]) -> ([2]); // 9
struct_construct<Unit>() -> ([3]); // 10
store_temp<RangeCheck>([2]) -> ([2]); // 11
store_temp<Unit>([3]) -> ([3]); // 12
return([2], [3]); // 13

test::u256_safe_divmod@0([0]: RangeCheck, [1]: core::integer::u256, [2]: NonZero<core::integer::u256>) -> (RangeCheck, Tuple<core::integer::u256, core::integer::u256>);
core::integer::U128MulGuaranteeDestruct::destruct@9([0]: RangeCheck, [1]: U128MulGuarantee) -> (RangeCheck, Unit);
"

aegis_spec "core::integer::U128MulGuaranteeDestruct::destruct" :=
  fun _ _ _ _ _ => True

aegis_spec "test::u256_safe_divmod" :=
  fun _ _ a b _ ρ =>
  U128_MOD * ZMod.val ρ.1.2 + ZMod.val ρ.1.1 =
    (U128_MOD * ZMod.val a.2 + ZMod.val a.1) / (U128_MOD * ZMod.val b.2 + ZMod.val b.1)
  ∧ U128_MOD * ZMod.val ρ.2.2 + ZMod.val ρ.2.1 =
    (U128_MOD * ZMod.val a.2 + ZMod.val a.1) % (U128_MOD * ZMod.val b.2 + ZMod.val b.1)

aegis_prove "test::u256_safe_divmod" :=
  fun _ _ a b _ ρ => by
  rintro ⟨_,_,h₁,h₂,rfl⟩
  exact ⟨h₁,h₂⟩

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
