import SierraLean.Commands

sierra_load_string "type felt252 = felt252;
type Array<felt252> = Array<felt252>;
type Box<felt252> = Box<felt252>;
type Unit = Struct<ut@Tuple>;
type core::option::Option::<core::box::Box::<core::felt252>> = Enum<ut@core::option::Option::<core::box::Box::<core::felt252>>, Box<felt252>, Unit>;

libfunc array_pop_front<felt252> = array_pop_front<felt252>;
libfunc branch_align = branch_align;
libfunc enum_init<core::option::Option::<core::box::Box::<core::felt252>>, 0> = enum_init<core::option::Option::<core::box::Box::<core::felt252>>, 0>;
libfunc store_temp<Array<felt252>> = store_temp<Array<felt252>>;
libfunc store_temp<core::option::Option::<core::box::Box::<core::felt252>>> = store_temp<core::option::Option::<core::box::Box::<core::felt252>>>;
libfunc jump = jump;
libfunc struct_construct<Unit> = struct_construct<Unit>;
libfunc enum_init<core::option::Option::<core::box::Box::<core::felt252>>, 1> = enum_init<core::option::Option::<core::box::Box::<core::felt252>>, 1>;
libfunc rename<Array<felt252>> = rename<Array<felt252>>;
libfunc rename<core::option::Option::<core::box::Box::<core::felt252>>> = rename<core::option::Option::<core::box::Box::<core::felt252>>>;

array_pop_front<felt252>([0]) { fallthrough([1], [2]) 6([3]) };
branch_align() -> ();
enum_init<core::option::Option::<core::box::Box::<core::felt252>>, 0>([2]) -> ([4]);
store_temp<Array<felt252>>([1]) -> ([5]);
store_temp<core::option::Option::<core::box::Box::<core::felt252>>>([4]) -> ([6]);
jump() { 11() };
branch_align() -> ();
struct_construct<Unit>() -> ([7]);
enum_init<core::option::Option::<core::box::Box::<core::felt252>>, 1>([7]) -> ([8]);
store_temp<Array<felt252>>([3]) -> ([5]);
store_temp<core::option::Option::<core::box::Box::<core::felt252>>>([8]) -> ([6]);
rename<Array<felt252>>([5]) -> ([9]);
rename<core::option::Option::<core::box::Box::<core::felt252>>>([6]) -> ([10]);
return([9], [10]);

test::foo@0([0]: Array<felt252>) -> (Array<felt252>, core::option::Option::<core::box::Box::<core::felt252>>);"

sierra_spec "test::foo" := fun _ a ρ₁ ρ₂ =>
  ρ₁ = a.tail ∧ ρ₂ = if a.length = 0 then .inr () else .inl a.head!

sierra_sound "test::foo" := fun _ a ρ₁ ρ₂ => by
  rintro ⟨_,_,(⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)⟩ <;> simp [«spec_test::foo»]

sierra_complete
