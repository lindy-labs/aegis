import Aegis.Commands

open Sierra

aegis_load_string "type RangeCheck = RangeCheck;
type felt252 = felt252;
type Array<felt252> = Array<felt252>;
type Snapshot<Array<felt252>> = Snapshot<Array<felt252>>;
type u32 = u32;
type Box<felt252> = Box<felt252>;
type Unit = Struct<ut@Tuple>;
type core::option::Option::<core::box::Box::<@core::felt252>> = Enum<ut@core::option::Option::<core::box::Box::<@core::felt252>>, Box<felt252>, Unit>;

libfunc array_get<felt252> = array_get<felt252>;
libfunc branch_align = branch_align;
libfunc enum_init<core::option::Option::<core::box::Box::<@core::felt252>>, 0> = enum_init<core::option::Option::<core::box::Box::<@core::felt252>>, 0>;
libfunc store_temp<RangeCheck> = store_temp<RangeCheck>;
libfunc store_temp<core::option::Option::<core::box::Box::<@core::felt252>>> = store_temp<core::option::Option::<core::box::Box::<@core::felt252>>>;
libfunc jump = jump;
libfunc struct_construct<Unit> = struct_construct<Unit>;
libfunc enum_init<core::option::Option::<core::box::Box::<@core::felt252>>, 1> = enum_init<core::option::Option::<core::box::Box::<@core::felt252>>, 1>;
libfunc rename<RangeCheck> = rename<RangeCheck>;
libfunc rename<core::option::Option::<core::box::Box::<@core::felt252>>> = rename<core::option::Option::<core::box::Box::<@core::felt252>>>;

array_get<felt252>([0], [1], [2]) { fallthrough([3], [4]) 6([5]) };
branch_align() -> ();
enum_init<core::option::Option::<core::box::Box::<@core::felt252>>, 0>([4]) -> ([6]);
store_temp<RangeCheck>([3]) -> ([7]);
store_temp<core::option::Option::<core::box::Box::<@core::felt252>>>([6]) -> ([8]);
jump() { 11() };
branch_align() -> ();
struct_construct<Unit>() -> ([9]);
enum_init<core::option::Option::<core::box::Box::<@core::felt252>>, 1>([9]) -> ([10]);
store_temp<RangeCheck>([5]) -> ([7]);
store_temp<core::option::Option::<core::box::Box::<@core::felt252>>>([10]) -> ([8]);
rename<RangeCheck>([7]) -> ([11]);
rename<core::option::Option::<core::box::Box::<@core::felt252>>>([8]) -> ([12]);
return([11], [12]);

test::foo@0([0]: RangeCheck, [1]: Snapshot<Array<felt252>>, [2]: u32) -> (RangeCheck, core::option::Option::<core::box::Box::<@core::felt252>>);"

aegis_spec "test::foo" := fun _ _ a i _ ρ =>
  ρ = if hl : i.val ≥ a.length then Sum.inr ()
      else Sum.inl (a.get ⟨i.val, lt_of_not_ge hl⟩)

aegis_prove "test::foo" := fun _ _ a i _ ρ => by
  rintro ⟨_, (h | h)⟩
  · rcases h with ⟨h, rfl⟩
    rw [eq_comm, List.get?_eq_some] at h
    rcases h with ⟨hl, rfl⟩
    simp [«spec_test::foo», not_le_of_gt hl]
  · rcases h with ⟨h, rfl⟩
    simp [«spec_test::foo», h]
