import Aegis.Commands

open Sierra

aegis_load_string "type u128 = u128 [storable: true, drop: true, dup: true, zero_sized: false];
type core::integer::u256 = Struct<ut@core::integer::u256, u128, u128> [storable: true, drop: true, dup: true, zero_sized: false];
type Box<core::integer::u256> = Box<core::integer::u256> [storable: true, drop: true, dup: true, zero_sized: false];
type Const<core::integer::u256, Const<u128, 16>, Const<u128, 32>> = Const<core::integer::u256, Const<u128, 16>, Const<u128, 32>> [storable: false, drop: false, dup: false, zero_sized: false];
type Const<u128, 32> = Const<u128, 32> [storable: false, drop: false, dup: false, zero_sized: false];
type Const<u128, 16> = Const<u128, 16> [storable: false, drop: false, dup: false, zero_sized: false];

libfunc const_as_immediate<Const<core::integer::u256, Const<u128, 16>, Const<u128, 32>>> = const_as_immediate<Const<core::integer::u256, Const<u128, 16>, Const<u128, 32>>>;
libfunc store_temp<core::integer::u256> = store_temp<core::integer::u256>;
libfunc const_as_box<Const<core::integer::u256, Const<u128, 16>, Const<u128, 32>>, 0> = const_as_box<Const<core::integer::u256, Const<u128, 16>, Const<u128, 32>>, 0>;

const_as_immediate<Const<core::integer::u256, Const<u128, 16>, Const<u128, 32>>>() -> ([0]); // 0
store_temp<core::integer::u256>([0]) -> ([0]); // 1
return([0]); // 2
const_as_immediate<Const<core::integer::u256, Const<u128, 16>, Const<u128, 32>>>() -> ([0]); // 3
store_temp<core::integer::u256>([0]) -> ([0]); // 4
return([0]); // 5
const_as_box<Const<core::integer::u256, Const<u128, 16>, Const<u128, 32>>, 0>() -> ([0]); // 6
return([0]); // 7
const_as_box<Const<core::integer::u256, Const<u128, 16>, Const<u128, 32>>, 0>() -> ([0]); // 8
return([0]); // 9

test::bar1@0() -> (core::integer::u256);
test::bar2@3() -> (core::integer::u256);
test::foo1@6() -> (Box<core::integer::u256>);
test::foo2@8() -> (Box<core::integer::u256>);"

aegis_spec "test::bar1" :=
  fun _ ρ =>
  ρ = (16, 32)

aegis_prove "test::bar1" :=
  fun _ ρ => by
  unfold «spec_test::bar1»
  aesop

aegis_spec "test::bar2" :=
  fun _ ρ =>
  ρ = (16, 32)

aegis_prove "test::bar2" :=
  fun _ ρ => by
  unfold «spec_test::bar2»
  aesop
