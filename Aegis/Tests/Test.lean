import Aegis.Analyzer

open Lean Meta Qq
namespace Sierra


def negParam := "type F = felt252;

libfunc c1 = felt252_const<-1>;
libfunc c2 = felt252_const<1>;
libfunc add = felt252_add;

c1() -> ([0]);
c2() -> ([1]);
add([0], [1]) -> ([2]);
return ([2]);


negparam@0() -> (F);"

#eval parseGrammar negParam
#eval analyzeFile negParam

def code01 := "
type core::option::Option::<core::integer::u128> = Enum<ut@core::option::Option::<core::integer::u128>, u128, Unit>;
type Tuple<u128> = Struct<ut@Tuple, u128>;
type Tuple<wad_ray::wad_ray::Wad> = Struct<ut@Tuple, wad_ray::wad_ray::Wad>;
type wad_ray::wad_ray::Ray = Struct<ut@wad_ray::wad_ray::Ray, u128>;
type Tuple<wad_ray::wad_ray::Ray> = Struct<ut@Tuple, wad_ray::wad_ray::Ray>;
type Tuple<u128, u128> = Struct<ut@Tuple, u128, u128>;"
#eval parseGrammar code01

def code02 := "type [0] = felt252;
libfunc [0] = felt252_const<5>;
[0]() -> ([5]);
return([5]);
foo@0([0]: [0] , [1]: [0]) -> ([0]);"
#eval parseGrammar code02
#eval analyzeFile code02

def code03 :=
"type [0] = felt252 [storable: true, drop: true, dup: false, zero_sized: false];

libfunc [0] = felt252_add;
libfunc [1] = drop<[0]>;
libfunc [2] = branch_align;
libfunc [3] = jump;

[3]() { 1() }; // 0
[0]([0], [1]) -> ([3]); // 1
[0]([3], [2]) -> ([4]); // 2
return([4]); // 3

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
libfunc [1] = felt252_const<4>; -- TODO test negative constants

[0]([0]) -> ([1]);
[1]() -> ([0]);
return([1]);

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
#eval parseGrammar e2etest_felt_add
#eval analyzeFile e2etest_felt_add

def test_enum_init :=
"type [0] = felt252;
type [1] = Enum<ut@foo, [0], [0]>;
type [2] = Enum<ut@bar, [1], [1]>;

libfunc [0] = enum_init<[1], 1>;
libfunc [1] = enum_init<[2], 1>;

[0]([0]) -> ([1]);
[1]([1]) -> ([2]);
return([2]);

foo@0([0]: [0]) -> ([2]);"
#eval parseGrammar test_enum_init
#eval analyzeFile test_enum_init

def test_enum_match :=
"type F = felt252;
type E = Enum<ut@foo, F, F>;

libfunc init = enum_init<E, 1>;
libfunc ematch = enum_match<E>;

init([0]) -> ([1]);
ematch([1]) { fallthrough([2]) 3([3]) };
return([2]);
return([3]);

foo@0([0]: F) -> (F);"
#eval parseGrammar test_enum_match
#eval analyzeFile test_enum_match

def test_struct_construct :=
"type F = felt252;
type S = Struct<ut@foo, F, F>;

libfunc construct = struct_construct<S>;

construct([0], [1]) -> ([2]);
return([2]);

foo@0([0]: F, [1]: F) -> (F);"
#eval parseGrammar test_struct_construct
#eval analyzeFile test_struct_construct

def test_struct_deconstruct :=
"type F = felt252;
type S = Struct<ut@foo, F, F>;

libfunc construct = struct_construct<S>;
libfunc deconstruct = struct_deconstruct<S>;

construct([0], [1]) -> ([2]);
deconstruct([2]) -> ([3], [4]);
return([3]);

foo@0([0]: F, [1]: F) -> (F);"
#eval parseGrammar test_struct_deconstruct
#eval analyzeFile test_struct_deconstruct

def test_struct_deconstruct' :=
"type F = felt252;
type S = Struct<ut@foo, F, F>;

libfunc construct = struct_construct<S>;
libfunc deconstruct = struct_deconstruct<S>;

construct([0], [0]) -> ([1]);
deconstruct([1]) -> ([2], [3]);
return([0]);

foo@0([0]: F) -> (F);"
#eval parseGrammar test_struct_deconstruct'
#eval analyzeFile test_struct_deconstruct'

def test_parse_tuples :=
"type felt252 = felt252;
type RangeCheck = RangeCheck;
type u128 = u128;
type Unit = Struct<ut@Tuple>;
type core::option::Option::<core::integer::u128> = Enum<ut@core::option::Option::<core::integer::u128>, u128, Unit>;
type Tuple<u128> = Struct<ut@Tuple, u128>;
type Array<felt252> = Array<felt252>;
type core::PanicResult::<(core::integer::u128,)> = Enum<ut@core::PanicResult::<(core::integer::u128,)>, Tuple<u128>, Array<felt252>>;"
#eval parseGrammar test_parse_tuples


def test_function_call_01 :=
"type F = felt252;

libfunc c5 = felt252_const<5>;
libfunc call = function_call<user@foo>;

c5() -> ([1]);
return([1]);
call([2]) -> ([3]);
return([3]);

foo@0([0]: F) -> (F);
bar@2([2]: F) -> (F);"
#eval parseGrammar test_function_call_01
#eval analyzeFile test_function_call_01 0

def test_parser_change :=
"type F = felt252;

libfunc c5 = felt252_const<5>;
libfunc call_bar = function_call<user@bar>;

c5() -> ([1]);
return([1]);
call_bar([2]) -> ([3]);
return([3]);

bar@0([0]: F) -> (F);
baz@2([2]: F) -> (F);"
#eval parseGrammar test_parser_change


def test_square_brackets :=
"type F = felt252;

libfunc c5 = felt252_const<5>;
libfunc call_bar = function_call<user@bar[expr42]>;

c5() -> ([1]);
return([1]);
call_bar([2]) -> ([3]);
return([3]);

bar[expr42]@0([0]: F) -> (F);
baz@2([2]: F) -> (F);"
#eval parseGrammar test_square_brackets
#eval analyzeFile test_square_brackets

def test_end :=
"libfunc function_call<user@foo::end> = function_call<user@foo::end::bar>;"
#eval parseGrammar test_end

def test_local :=
"type F = felt252;

libfunc a = alloc_local<F>;
libfunc s = store_local<F>;

a() -> ([1]);
s([1], [0]) -> ([2]);
return([2]);

foo@0([0]: F) -> (F);"
#eval parseGrammar test_local
#eval analyzeFile test_local
