import Aegis.Commands
import Aegis.Tactic

namespace Sierra.Test.EnumIdx

aegis_load_string "type BoundedInt<0, 4> = BoundedInt<0, 4> [storable: true, drop: true, dup: true, zero_sized: false];
type Unit = Struct<ut@Tuple> [storable: true, drop: true, dup: true, zero_sized: true];
type test::IndexEnum5 = Enum<ut@test::IndexEnum5, Unit, Unit, Unit, Unit, Unit> [storable: true, drop: true, dup: true, zero_sized: false];

libfunc enum_from_bounded_int<test::IndexEnum5> = enum_from_bounded_int<test::IndexEnum5>;
libfunc store_temp<test::IndexEnum5> = store_temp<test::IndexEnum5>;

F0:
enum_from_bounded_int<test::IndexEnum5>([0]) -> ([1]);
store_temp<test::IndexEnum5>([1]) -> ([1]);
return([1]);

test::foo@F0([0]: BoundedInt<0, 4>) -> (test::IndexEnum5);"

aegis_spec "test::foo" :=
  fun _ a ρ =>
  ρ = UnitEnum.fromIdx 4 a.toNat

aegis_prove "test::foo" :=
  fun _ a ρ => by
  unfold_spec "test::foo"
  rintro rfl
  rfl
