import Aegis.Commands

open Sierra

aegis_load_file "ternary_add.sierra"

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

aegis_load_file "double.sierra"

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

aegis_load_string "type Array<felt252> = Array<felt252> [storable: true, drop: true, dup: false, zero_sized: false];
type Snapshot<Array<felt252>> = Snapshot<Array<felt252>> [storable: true, drop: true, dup: true, zero_sized: false];
type Unit = Struct<ut@Tuple> [storable: true, drop: true, dup: true, zero_sized: true];
type felt252 = felt252 [storable: true, drop: true, dup: true, zero_sized: false];
type Box<felt252> = Box<felt252> [storable: true, drop: true, dup: true, zero_sized: false];
type core::option::Option::<core::box::Box::<@core::felt252>> = Enum<ut@core::option::Option::<core::box::Box::<@core::felt252>>, Box<felt252>, Unit> [storable: true, drop: true, dup: true, zero_sized: false];

libfunc array_snapshot_pop_front<felt252> = array_snapshot_pop_front<felt252>;
libfunc branch_align = branch_align;
libfunc enum_init<core::option::Option::<core::box::Box::<@core::felt252>>, 0> = enum_init<core::option::Option::<core::box::Box::<@core::felt252>>, 0>;
libfunc store_temp<Snapshot<Array<felt252>>> = store_temp<Snapshot<Array<felt252>>>;
libfunc store_temp<core::option::Option::<core::box::Box::<@core::felt252>>> = store_temp<core::option::Option::<core::box::Box::<@core::felt252>>>;
libfunc jump = jump;
libfunc struct_construct<Unit> = struct_construct<Unit>;
libfunc enum_init<core::option::Option::<core::box::Box::<@core::felt252>>, 1> = enum_init<core::option::Option::<core::box::Box::<@core::felt252>>, 1>;

array_snapshot_pop_front<felt252>([0]) { fallthrough([1], [2]) 6([3]) }; // 0
branch_align() -> (); // 1
enum_init<core::option::Option::<core::box::Box::<@core::felt252>>, 0>([2]) -> ([4]); // 2
store_temp<Snapshot<Array<felt252>>>([1]) -> ([5]); // 3
store_temp<core::option::Option::<core::box::Box::<@core::felt252>>>([4]) -> ([6]); // 4
jump() { 11() }; // 5
branch_align() -> (); // 6
struct_construct<Unit>() -> ([7]); // 7
enum_init<core::option::Option::<core::box::Box::<@core::felt252>>, 1>([7]) -> ([8]); // 8
store_temp<Snapshot<Array<felt252>>>([3]) -> ([5]); // 9
store_temp<core::option::Option::<core::box::Box::<@core::felt252>>>([8]) -> ([6]); // 10
return([5], [6]); // 11

test::array_snapshot_pop_front@0([0]: Snapshot<Array<felt252>>) -> (Snapshot<Array<felt252>>, core::option::Option::<core::box::Box::<@core::felt252>>);
"

aegis_spec "test::array_snapshot_pop_front" :=
  fun m a ρ₁ ρ₂ =>
  (a ≠ [] ∧ ρ₁ = a.tail ∧ ∃ n a', m.boxHeap .Felt252 n = .some a' ∧ ρ₂ = .inl n)
  ∨ (a = [] ∧ ρ₁ = [] ∧ ρ₂ = .inr ())

aegis_prove"test::array_snapshot_pop_front" :=
  fun m a ρ₁ ρ₂ => by
  unfold «spec_test::array_snapshot_pop_front»
  aesop

aegis_load_string "type GasBuiltin = GasBuiltin [storable: true, drop: false, dup: false, zero_sized: false];
type Box<core::starknet::info::ExecutionInfo> = Box<core::starknet::info::ExecutionInfo> [storable: true, drop: true, dup: true, zero_sized: false];
type Array<felt252> = Array<felt252> [storable: true, drop: true, dup: false, zero_sized: false];
type core::result::Result::<core::box::Box::<core::starknet::info::ExecutionInfo>, core::array::Array::<core::felt252>> = Enum<ut@core::result::Result::<core::box::Box::<core::starknet::info::ExecutionInfo>, core::array::Array::<core::felt252>>, Box<core::starknet::info::ExecutionInfo>, Array<felt252>> [storable: true, drop: true, dup: false, zero_sized: false];
type felt252 = felt252 [storable: true, drop: true, dup: true, zero_sized: false];
type Box<core::starknet::info::BlockInfo> = Box<core::starknet::info::BlockInfo> [storable: true, drop: true, dup: true, zero_sized: false];
type Box<core::starknet::info::TxInfo> = Box<core::starknet::info::TxInfo> [storable: true, drop: true, dup: true, zero_sized: false];
type ContractAddress = ContractAddress [storable: true, drop: true, dup: true, zero_sized: false];
type core::starknet::info::ExecutionInfo = Struct<ut@core::starknet::info::ExecutionInfo, Box<core::starknet::info::BlockInfo>, Box<core::starknet::info::TxInfo>, ContractAddress, ContractAddress, felt252> [storable: true, drop: true, dup: true, zero_sized: false];
type u128 = u128 [storable: true, drop: true, dup: true, zero_sized: false];
type Snapshot<Array<felt252>> = Snapshot<Array<felt252>> [storable: true, drop: true, dup: true, zero_sized: false];
type core::array::Span::<core::felt252> = Struct<ut@core::array::Span::<core::felt252>, Snapshot<Array<felt252>>> [storable: true, drop: true, dup: true, zero_sized: false];
type core::starknet::info::TxInfo = Struct<ut@core::starknet::info::TxInfo, felt252, ContractAddress, u128, core::array::Span::<core::felt252>, felt252, felt252, felt252> [storable: true, drop: true, dup: true, zero_sized: false];
type u64 = u64 [storable: true, drop: true, dup: true, zero_sized: false];
type core::starknet::info::BlockInfo = Struct<ut@core::starknet::info::BlockInfo, u64, u64, ContractAddress> [storable: true, drop: true, dup: true, zero_sized: false];
type System = System [storable: true, drop: false, dup: false, zero_sized: false];

libfunc get_execution_info_syscall = get_execution_info_syscall;
libfunc branch_align = branch_align;
libfunc enum_init<core::result::Result::<core::box::Box::<core::starknet::info::ExecutionInfo>, core::array::Array::<core::felt252>>, 0> = enum_init<core::result::Result::<core::box::Box::<core::starknet::info::ExecutionInfo>, core::array::Array::<core::felt252>>, 0>;
libfunc store_temp<GasBuiltin> = store_temp<GasBuiltin>;
libfunc store_temp<System> = store_temp<System>;
libfunc store_temp<core::result::Result::<core::box::Box::<core::starknet::info::ExecutionInfo>, core::array::Array::<core::felt252>>> = store_temp<core::result::Result::<core::box::Box::<core::starknet::info::ExecutionInfo>, core::array::Array::<core::felt252>>>;
libfunc jump = jump;
libfunc enum_init<core::result::Result::<core::box::Box::<core::starknet::info::ExecutionInfo>, core::array::Array::<core::felt252>>, 1> = enum_init<core::result::Result::<core::box::Box::<core::starknet::info::ExecutionInfo>, core::array::Array::<core::felt252>>, 1>;

get_execution_info_syscall([0], [1]) { fallthrough([2], [3], [4]) 7([5], [6], [7]) }; // 0
branch_align() -> (); // 1
enum_init<core::result::Result::<core::box::Box::<core::starknet::info::ExecutionInfo>, core::array::Array::<core::felt252>>, 0>([4]) -> ([8]); // 2
store_temp<GasBuiltin>([2]) -> ([9]); // 3
store_temp<System>([3]) -> ([10]); // 4
store_temp<core::result::Result::<core::box::Box::<core::starknet::info::ExecutionInfo>, core::array::Array::<core::felt252>>>([8]) -> ([11]); // 5
jump() { 12() }; // 6
branch_align() -> (); // 7
enum_init<core::result::Result::<core::box::Box::<core::starknet::info::ExecutionInfo>, core::array::Array::<core::felt252>>, 1>([7]) -> ([12]); // 8
store_temp<GasBuiltin>([5]) -> ([9]); // 9
store_temp<System>([6]) -> ([10]); // 10
store_temp<core::result::Result::<core::box::Box::<core::starknet::info::ExecutionInfo>, core::array::Array::<core::felt252>>>([12]) -> ([11]); // 11
return([9], [10], [11]); // 12

test::get_execution_info@0([0]: GasBuiltin, [1]: System) -> (GasBuiltin, System, core::result::Result::<core::box::Box::<core::starknet::info::ExecutionInfo>, core::array::Array::<core::felt252>>);
"

aegis_spec "test::get_execution_info" :=
  fun m _ s _ s' ρ =>
  s = s' ∧
  ((∃ rei rbi rti, ρ = .inl rei ∧
      m.boxHeap .ExecutionInfo rei = .some ⟨rbi, rti,
      m.callerAddress, m.contractAddress, m.entryPointSelector⟩
      ∧ m.boxHeap .BlockInfo rbi = .some ⟨m.blockNumber, m.blockTimestamp, m.sequencerAddress⟩
      ∧ m.boxHeap .TxInfo rti = .some ⟨m.txVersion, m.txContract, m.txMaxFee, m.txSignature,
        m.txHash, m.txChainIdentifier, m.txNonce⟩)
    ∨ ρ.isRight)

aegis_prove "test::get_execution_info" :=
  fun m _ s _ s' ρ => by
  unfold «spec_test::get_execution_info»
  rintro ⟨_,_,(⟨⟨_,_,_,_,_,h₁,h₂,h₃,rfl,rfl,rfl⟩,rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · exact ⟨rfl, .inl ⟨_,_,_,rfl,h₁,h₂,h₃⟩⟩
  · exact ⟨rfl, .inr rfl⟩

aegis_load_string "type Box<felt252> = Box<felt252> [storable: true, drop: true, dup: true, zero_sized: false];
type Nullable<felt252> = Nullable<felt252> [storable: true, drop: true, dup: true, zero_sized: false];
type felt252 = felt252 [storable: true, drop: true, dup: true, zero_sized: false];

libfunc nullable_from_box<felt252> = nullable_from_box<felt252>;
libfunc store_temp<Nullable<felt252>> = store_temp<Nullable<felt252>>;

nullable_from_box<felt252>([0]) -> ([1]); // 0
store_temp<Nullable<felt252>>([1]) -> ([1]); // 1
return([1]); // 2

test::nullable_from_box@0([0]: Box<felt252>) -> (Nullable<felt252>);"

aegis_spec "test::nullable_from_box" :=
  fun m a ρ =>
  ρ = m.boxHeap .Felt252 a

aegis_prove "test::nullable_from_box" :=
  fun m a ρ => by
  rintro rfl
  rfl

aegis_load_string "type Nullable<felt252> = Nullable<felt252> [storable: true, drop: true, dup: true, zero_sized: false];
type Box<felt252> = Box<felt252> [storable: true, drop: true, dup: true, zero_sized: false];
type felt252 = felt252 [storable: true, drop: true, dup: true, zero_sized: false];

libfunc match_nullable<felt252> = match_nullable<felt252>;
libfunc branch_align = branch_align;
libfunc store_temp<Box<felt252>> = store_temp<Box<felt252>>;
libfunc jump = jump;
libfunc drop<Box<felt252>> = drop<Box<felt252>>;

match_nullable<felt252>([0]) { fallthrough() 4([2]) }; // 0
branch_align() -> (); // 1
store_temp<Box<felt252>>([1]) -> ([3]); // 2
jump() { 7() }; // 3
branch_align() -> (); // 4
drop<Box<felt252>>([1]) -> (); // 5
store_temp<Box<felt252>>([2]) -> ([3]); // 6
return([3]); // 7

test::match_nullable@0([0]: Nullable<felt252>, [1]: Box<felt252>) -> (Box<felt252>);"

aegis_spec "test::match_nullable" :=
  fun m a b ρ =>
  (a = .none ∧ ρ = b)
  ∨ (a = m.boxHeap .Felt252 ρ)

aegis_prove "test::match_nullable" :=
  fun m a b ρ => by
  unfold «spec_test::match_nullable»
  rintro ⟨_,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · aesop
  · aesop

aegis_load_string "type u16 = u16 [storable: true, drop: true, dup: true, zero_sized: false];
type u64 = u64 [storable: true, drop: true, dup: true, zero_sized: false];

libfunc upcast<u16, u64> = upcast<u16, u64>;
libfunc store_temp<u64> = store_temp<u64>;

upcast<u16, u64>([0]) -> ([1]); // 0
store_temp<u64>([1]) -> ([1]); // 1
return([1]); // 2

test::upcast@0([0]: u16) -> (u64);"

aegis_spec "test::upcast" :=
  fun _ a ρ =>
  ρ = a.cast

aegis_prove "test::upcast" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_load_string "type u64 = u64 [storable: true, drop: true, dup: true, zero_sized: false];

libfunc upcast<u64, u64> = upcast<u64, u64>;
libfunc store_temp<u64> = store_temp<u64>;

upcast<u64, u64>([0]) -> ([1]); // 0
store_temp<u64>([1]) -> ([1]); // 1
return([1]); // 2

test::upcast_refl@0([0]: u64) -> (u64);"

aegis_spec "test::upcast_refl" :=
  fun _ a ρ =>
  ρ = a

aegis_prove "test::upcast_refl" :=
  fun _ a ρ => by
  rintro rfl
  rfl

aegis_load_string "type RangeCheck = RangeCheck [storable: true, drop: false, dup: false, zero_sized: false];
type Unit = Struct<ut@Tuple> [storable: true, drop: true, dup: true, zero_sized: true];
type u16 = u16 [storable: true, drop: true, dup: true, zero_sized: false];
type core::option::Option::<core::integer::u16> = Enum<ut@core::option::Option::<core::integer::u16>, u16, Unit> [storable: true, drop: true, dup: true, zero_sized: false];
type u64 = u64 [storable: true, drop: true, dup: true, zero_sized: false];

libfunc downcast<u64, u16> = downcast<u64, u16>;
libfunc branch_align = branch_align;
libfunc enum_init<core::option::Option::<core::integer::u16>, 0> = enum_init<core::option::Option::<core::integer::u16>, 0>;
libfunc store_temp<RangeCheck> = store_temp<RangeCheck>;
libfunc store_temp<core::option::Option::<core::integer::u16>> = store_temp<core::option::Option::<core::integer::u16>>;
libfunc struct_construct<Unit> = struct_construct<Unit>;
libfunc enum_init<core::option::Option::<core::integer::u16>, 1> = enum_init<core::option::Option::<core::integer::u16>, 1>;

downcast<u64, u16>([0], [1]) { fallthrough([2], [3]) 6([4]) }; // 0
branch_align() -> (); // 1
enum_init<core::option::Option::<core::integer::u16>, 0>([3]) -> ([5]); // 2
store_temp<RangeCheck>([2]) -> ([2]); // 3
store_temp<core::option::Option::<core::integer::u16>>([5]) -> ([5]); // 4
return([2], [5]); // 5
branch_align() -> (); // 6
struct_construct<Unit>() -> ([6]); // 7
enum_init<core::option::Option::<core::integer::u16>, 1>([6]) -> ([7]); // 8
store_temp<RangeCheck>([4]) -> ([4]); // 9
store_temp<core::option::Option::<core::integer::u16>>([7]) -> ([7]); // 10
return([4], [7]); // 11

test::downcast@0([0]: RangeCheck, [1]: u64) -> (RangeCheck, core::option::Option::<core::integer::u16>);"

aegis_spec "test::downcast" :=
  fun _ _ a _ ρ =>
  ρ = if a.val < U16_MOD then .inl a.cast else .inr ()

aegis_prove "test::downcast" :=
  fun _ _ a _ ρ => by
  unfold «spec_test::downcast»
  aesop (add forward safe Nat.lt_le_asymm)

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
