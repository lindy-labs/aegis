import SierraLean.Analyzer

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
libfunc [4] = store_temp<[0]>;
[4]([0]) -> ([1]);
return([1]);
[0]@0([0]: [0]) -> ([0]);"
#eval parseGrammar code04

#eval analyzeFile code04
