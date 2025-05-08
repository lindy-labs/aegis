import Aegis.Commands
import Aegis.Tactic

namespace Sierra.Test.BoundedInt.BoundedIntAdd

aegis_load_string "type i8 = i8 [storable: true, drop: true, dup: true, zero_sized: false];
type BoundedInt<-256, 254> = BoundedInt<-256, 254> [storable: true, drop: true, dup: true, zero_sized: false];

libfunc bounded_int_add<i8, i8> = bounded_int_add<i8, i8>;
libfunc store_temp<BoundedInt<-256, 254>> = store_temp<BoundedInt<-256, 254>>;

F0:
bounded_int_add<i8, i8>([0], [1]) -> ([2]);
store_temp<BoundedInt<-256, 254>>([2]) -> ([2]);
return([2]);

test::foo@F0([0]: i8, [1]: i8) -> (BoundedInt<-256, 254>);
"

aegis_spec "test::foo" :=
  fun _ a b ρ =>
  ρ = a.toInt + b.toInt

aegis_prove "test::foo" :=
  fun _ a b ρ => by
  rintro rfl
  rfl

aegis_complete
