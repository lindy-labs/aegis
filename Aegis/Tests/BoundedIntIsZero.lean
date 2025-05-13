import Aegis.Commands
import Aegis.Tactic

namespace Sierra.Test.BoundedInt.BoundedIntIsZero

aegis_load_string "type BoundedInt<0, 680564733841876926926749214863536422911> = BoundedInt<0, 680564733841876926926749214863536422911> [storable: true, drop: true, dup: true, zero_sized: false];
type Unit = Struct<ut@Tuple> [storable: true, drop: true, dup: true, zero_sized: true];
type NonZero<BoundedInt<0, 680564733841876926926749214863536422911>> = NonZero<BoundedInt<0, 680564733841876926926749214863536422911>> [storable: true, drop: true, dup: true, zero_sized: false];
type core::zeroable::IsZeroResult::<test::BoundedInt::<0, 680564733841876926926749214863536422911>> = Enum<ut@core::zeroable::IsZeroResult::<test::BoundedInt::<0, 680564733841876926926749214863536422911>>, Unit, NonZero<BoundedInt<0, 680564733841876926926749214863536422911>>> [storable: true, drop: true, dup: true, zero_sized: false];

libfunc bounded_int_is_zero<BoundedInt<0, 680564733841876926926749214863536422911>> = bounded_int_is_zero<BoundedInt<0, 680564733841876926926749214863536422911>>;
libfunc branch_align = branch_align;
libfunc struct_construct<Unit> = struct_construct<Unit>;
libfunc enum_init<core::zeroable::IsZeroResult::<test::BoundedInt::<0, 680564733841876926926749214863536422911>>, 0> = enum_init<core::zeroable::IsZeroResult::<test::BoundedInt::<0, 680564733841876926926749214863536422911>>, 0>;
libfunc store_temp<core::zeroable::IsZeroResult::<test::BoundedInt::<0, 680564733841876926926749214863536422911>>> = store_temp<core::zeroable::IsZeroResult::<test::BoundedInt::<0, 680564733841876926926749214863536422911>>>;
libfunc enum_init<core::zeroable::IsZeroResult::<test::BoundedInt::<0, 680564733841876926926749214863536422911>>, 1> = enum_init<core::zeroable::IsZeroResult::<test::BoundedInt::<0, 680564733841876926926749214863536422911>>, 1>;

F0:
bounded_int_is_zero<BoundedInt<0, 680564733841876926926749214863536422911>>([0]) { fallthrough() F0_B0([1]) };
branch_align() -> ();
struct_construct<Unit>() -> ([2]);
enum_init<core::zeroable::IsZeroResult::<test::BoundedInt::<0, 680564733841876926926749214863536422911>>, 0>([2]) -> ([3]);
store_temp<core::zeroable::IsZeroResult::<test::BoundedInt::<0, 680564733841876926926749214863536422911>>>([3]) -> ([3]);
return([3]);
F0_B0:
branch_align() -> ();
enum_init<core::zeroable::IsZeroResult::<test::BoundedInt::<0, 680564733841876926926749214863536422911>>, 1>([1]) -> ([4]);
store_temp<core::zeroable::IsZeroResult::<test::BoundedInt::<0, 680564733841876926926749214863536422911>>>([4]) -> ([4]);
return([4]);

test::foo@F0([0]: BoundedInt<0, 680564733841876926926749214863536422911>) -> (core::zeroable::IsZeroResult::<test::BoundedInt::<0, 680564733841876926926749214863536422911>>);"

aegis_spec "test::foo" :=
  fun _ a ρ =>
  a = 0 ∧ ρ.isLeft ∨
    a ≠ 0 ∧ ρ = .inr a

aegis_prove "test::foo" :=
  fun _ a ρ => by
  unfold_spec "test::foo"
  aesop
