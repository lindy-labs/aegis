import SierraLean.Analyzer

open Lean Meta Qq
namespace Sierra

def code01 := "
type core::option::Option::<core::integer::u128> = Enum<ut@core::option::Option::<core::integer::u128>, u128, Unit>;
type Tuple<u128> = Struct<ut@Tuple, u128>;
type Tuple<wad_ray::wad_ray::Wad> = Struct<ut@Tuple, wad_ray::wad_ray::Wad>;
type wad_ray::wad_ray::Ray = Struct<ut@wad_ray::wad_ray::Ray, u128>;
type Tuple<wad_ray::wad_ray::Ray> = Struct<ut@Tuple, wad_ray::wad_ray::Ray>;
type Tuple<u128, u128> = Struct<ut@Tuple, u128, u128>;"
#eval parseGrammar code01  -- TODO any bigger than this and we run out of stack space, not sure what to do about it

def code02 := "type [0] = felt252;
libfunc [0] = felt252_const<5>;
[0]() { 1([5]) };
return([2]);
[0]@0([0]: [0] , [1]: [0]) -> ([2]);"
#eval parseGrammar code01

def code03 :=
"type [0] = felt252;
libfunc [0] = felt252_add;
libfunc [1] = drop<[0]>;
libfunc [2] = branch_align;
libfunc [3] = jump;
[3]() { 1() };
[0]([0], [1]) -> ([3]);
[0]([3], [2]) -> ([4]);
return([4]);
[0]@0([0]: [0], [1]: [0], [2]: [0]) -> ([0]);"
#eval analyzeFile code03


def code04 :=
"type [0] = felt252;
type [1] = NonZero<[0]>;

libfunc [2] = felt252_const<5>;
libfunc [3] = dup<[0]>;
libfunc [1] = felt252_sub;
libfunc [9] = store_temp<[0]>;
libfunc [0] = felt252_is_zero;
libfunc [4] = branch_align;
libfunc [5] = drop<[0]>;
libfunc [6] = felt252_const<0>;
libfunc [7] = jump;
libfunc [8] = drop<[1]>;
libfunc [10] = rename<[0]>;

[2]() -> ([1]);
[3]([0]) -> ([0], [3]);
[1]([3], [1]) -> ([2]);
[9]([2]) -> ([2]);
[0]([2]) { fallthrough() 10([4]) };
[4]() -> ();
[5]([0]) -> ();
[6]() -> ([5]);
[9]([5]) -> ([6]);
[7]() { 13() };
[4]() -> ();
[8]([4]) -> ();
[9]([0]) -> ([6]);
[10]([6]) -> ([7]);
return([7]);

[0]@0([0]: [0]) -> ([0]);"
#eval parseGrammar code04
#eval analyzeFile code04

/-- Tests the genration of fresh names. -/
def code05 :=
"type [0] = felt252;
libfunc [0] = rename<[0]>;
libfunc [1] = felt252_const<4>;
[0]([0]) -> ([1]);
[1]() -> ([0]);
return([0]);
foo@0([0]: [0]) -> ([0]);"
#eval parseGrammar code05
#eval analyzeFile code05

def e2etest_felt_add :=
"type felt252 = felt252;

libfunc dup<felt252> = dup<felt252>;
libfunc felt252_add = felt252_add;
libfunc drop<felt252> = drop<felt252>;
libfunc store_temp<felt252> = store_temp<felt252>;

dup<felt252>([0]) -> ([0], [3]);
dup<felt252>([1]) -> ([1], [4]);
felt252_add([3], [4]) -> ([2]);
drop<felt252>([2]) -> ();
felt252_add([0], [1]) -> ([5]);
store_temp<felt252>([5]) -> ([6]);
return([6]);

test::foo@0([0]: felt252, [1]: felt252) -> (felt252);"
#eval analyzeFile e2etest_felt_add