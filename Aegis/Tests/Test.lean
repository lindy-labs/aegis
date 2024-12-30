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

/--
info: Except.ok { typedefs := [(Sierra.Identifier.name "F" [] none, Sierra.Identifier.name "felt252" [] none)],
  libfuncs := [(Sierra.Identifier.name "c1" [] none,
                Sierra.Identifier.name "felt252_const" [Sierra.Parameter.const -1] none),
               (Sierra.Identifier.name "c2" [] none,
                Sierra.Identifier.name "felt252_const" [Sierra.Parameter.const 1] none),
               (Sierra.Identifier.name "add" [] none, Sierra.Identifier.name "felt252_add" [] none)],
  statements := [{ libfunc_id := Sierra.Identifier.name "c1" [] none,
                   args := [],
                   branches := [{ target := none, results := [0] }] },
                 { libfunc_id := Sierra.Identifier.name "c2" [] none,
                   args := [],
                   branches := [{ target := none, results := [1] }] },
                 { libfunc_id := Sierra.Identifier.name "add" [] none,
                   args := [0, 1],
                   branches := [{ target := none, results := [2] }] },
                 { libfunc_id := Sierra.Identifier.name "return" [] none, args := [2], branches := [] }],
  declarations := [(Sierra.Identifier.name "negparam" [] none, 0, [], [Sierra.Identifier.name "F" [] none])] }
-/
#guard_msgs in
#eval parseGrammar negParam
/--
info: fun m ρ => ↑(Int.negSucc 0) + ↑(Int.ofNat 1) = ρ
 Inferred Type:Sierra.Metadata → Sierra.F → Prop
-/
#guard_msgs in
#eval analyzeFile negParam

def code01 := "
type core::option::Option::<core::integer::u128> = Enum<ut@core::option::Option::<core::integer::u128>, u128, Unit>;
type Tuple<u128> = Struct<ut@Tuple, u128>;
type Tuple<wad_ray::wad_ray::Wad> = Struct<ut@Tuple, wad_ray::wad_ray::Wad>;
type wad_ray::wad_ray::Ray = Struct<ut@wad_ray::wad_ray::Ray, u128>;
type Tuple<wad_ray::wad_ray::Ray> = Struct<ut@Tuple, wad_ray::wad_ray::Ray>;
type Tuple<u128, u128> = Struct<ut@Tuple, u128, u128>;"
/--
info: Except.ok { typedefs := [(Sierra.Identifier.name
                  "core"
                  []
                  (some (Sierra.Identifier.name
                     "option"
                     []
                     (some (Sierra.Identifier.name
                        "Option"
                        [Sierra.Parameter.identifier
                           (Sierra.Identifier.name
                             "core"
                             []
                             (some (Sierra.Identifier.name
                                "integer"
                                []
                                (some (Sierra.Identifier.name "u128" [] none)))))]
                        none)))),
                Sierra.Identifier.name
                  "Enum"
                  [Sierra.Parameter.usertype
                     (Sierra.Identifier.name
                       "core"
                       []
                       (some (Sierra.Identifier.name
                          "option"
                          []
                          (some (Sierra.Identifier.name
                             "Option"
                             [Sierra.Parameter.identifier
                                (Sierra.Identifier.name
                                  "core"
                                  []
                                  (some (Sierra.Identifier.name
                                     "integer"
                                     []
                                     (some (Sierra.Identifier.name "u128" [] none)))))]
                             none))))),
                   Sierra.Parameter.identifier (Sierra.Identifier.name "u128" [] none),
                   Sierra.Parameter.identifier (Sierra.Identifier.name "Unit" [] none)]
                  none),
               (Sierra.Identifier.name
                  "Tuple"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "u128" [] none)]
                  none,
                Sierra.Identifier.name
                  "Struct"
                  [Sierra.Parameter.usertype (Sierra.Identifier.name "Tuple" [] none),
                   Sierra.Parameter.identifier (Sierra.Identifier.name "u128" [] none)]
                  none),
               (Sierra.Identifier.name
                  "Tuple"
                  [Sierra.Parameter.identifier
                     (Sierra.Identifier.name
                       "wad_ray"
                       []
                       (some (Sierra.Identifier.name "wad_ray" [] (some (Sierra.Identifier.name "Wad" [] none)))))]
                  none,
                Sierra.Identifier.name
                  "Struct"
                  [Sierra.Parameter.usertype (Sierra.Identifier.name "Tuple" [] none),
                   Sierra.Parameter.identifier
                     (Sierra.Identifier.name
                       "wad_ray"
                       []
                       (some (Sierra.Identifier.name "wad_ray" [] (some (Sierra.Identifier.name "Wad" [] none)))))]
                  none),
               (Sierra.Identifier.name
                  "wad_ray"
                  []
                  (some (Sierra.Identifier.name "wad_ray" [] (some (Sierra.Identifier.name "Ray" [] none)))),
                Sierra.Identifier.name
                  "Struct"
                  [Sierra.Parameter.usertype
                     (Sierra.Identifier.name
                       "wad_ray"
                       []
                       (some (Sierra.Identifier.name "wad_ray" [] (some (Sierra.Identifier.name "Ray" [] none))))),
                   Sierra.Parameter.identifier (Sierra.Identifier.name "u128" [] none)]
                  none),
               (Sierra.Identifier.name
                  "Tuple"
                  [Sierra.Parameter.identifier
                     (Sierra.Identifier.name
                       "wad_ray"
                       []
                       (some (Sierra.Identifier.name "wad_ray" [] (some (Sierra.Identifier.name "Ray" [] none)))))]
                  none,
                Sierra.Identifier.name
                  "Struct"
                  [Sierra.Parameter.usertype (Sierra.Identifier.name "Tuple" [] none),
                   Sierra.Parameter.identifier
                     (Sierra.Identifier.name
                       "wad_ray"
                       []
                       (some (Sierra.Identifier.name "wad_ray" [] (some (Sierra.Identifier.name "Ray" [] none)))))]
                  none),
               (Sierra.Identifier.name
                  "Tuple"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "u128" [] none),
                   Sierra.Parameter.identifier (Sierra.Identifier.name "u128" [] none)]
                  none,
                Sierra.Identifier.name
                  "Struct"
                  [Sierra.Parameter.usertype (Sierra.Identifier.name "Tuple" [] none),
                   Sierra.Parameter.identifier (Sierra.Identifier.name "u128" [] none),
                   Sierra.Parameter.identifier (Sierra.Identifier.name "u128" [] none)]
                  none)],
  libfuncs := [],
  statements := [],
  declarations := [] }-/
#guard_msgs in
#eval parseGrammar code01

def code02 := "type [0] = felt252;
libfunc [0] = felt252_const<5>;
[0]() -> ([5]);
return([5]);
foo@0([0]: [0] , [1]: [0]) -> ([0]);"
/--
info: Except.ok { typedefs := [(Sierra.Identifier.ref 0, Sierra.Identifier.name "felt252" [] none)],
  libfuncs := [(Sierra.Identifier.ref 0, Sierra.Identifier.name "felt252_const" [Sierra.Parameter.const 5] none)],
  statements := [{ libfunc_id := Sierra.Identifier.ref 0,
                   args := [],
                   branches := [{ target := none, results := [5] }] },
                 { libfunc_id := Sierra.Identifier.name "return" [] none, args := [5], branches := [] }],
  declarations := [(Sierra.Identifier.name "foo" [] none,
                    0,
                    [(0, Sierra.Identifier.ref 0), (1, Sierra.Identifier.ref 0)],
                    [Sierra.Identifier.ref 0])] } -/
#guard_msgs in
#eval parseGrammar code02
/--
info: fun m ref0 ref1 ρ => ↑(Int.ofNat 5) = ρ
 Inferred Type:Sierra.Metadata → Sierra.F → Sierra.F → Sierra.F → Prop -/
#guard_msgs in
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
/--
info: fun m ref0 ref1 ref2 ρ => ref0 + ref1 + ref2 = ρ
 Inferred Type:Sierra.Metadata → Sierra.F → Sierra.F → Sierra.F → Sierra.F → Prop -/
#guard_msgs in
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
/--
info: Except.ok { typedefs := [(Sierra.Identifier.ref 0, Sierra.Identifier.name "felt252" [] none),
               (Sierra.Identifier.ref 1,
                Sierra.Identifier.name "NonZero" [Sierra.Parameter.identifier (Sierra.Identifier.ref 0)] none)],
  libfuncs := [(Sierra.Identifier.ref 2, Sierra.Identifier.name "felt252_const" [Sierra.Parameter.const 5] none),
               (Sierra.Identifier.ref 3,
                Sierra.Identifier.name "dup" [Sierra.Parameter.identifier (Sierra.Identifier.ref 0)] none),
               (Sierra.Identifier.ref 1, Sierra.Identifier.name "felt252_sub" [] none),
               (Sierra.Identifier.ref 9,
                Sierra.Identifier.name "store_temp" [Sierra.Parameter.identifier (Sierra.Identifier.ref 0)] none),
               (Sierra.Identifier.ref 0, Sierra.Identifier.name "felt252_is_zero" [] none),
               (Sierra.Identifier.ref 4, Sierra.Identifier.name "branch_align" [] none),
               (Sierra.Identifier.ref 5,
                Sierra.Identifier.name "drop" [Sierra.Parameter.identifier (Sierra.Identifier.ref 0)] none),
               (Sierra.Identifier.ref 6, Sierra.Identifier.name "felt252_const" [Sierra.Parameter.const 0] none),
               (Sierra.Identifier.ref 7, Sierra.Identifier.name "jump" [] none),
               (Sierra.Identifier.ref 8,
                Sierra.Identifier.name "drop" [Sierra.Parameter.identifier (Sierra.Identifier.ref 1)] none),
               (Sierra.Identifier.ref 10,
                Sierra.Identifier.name "rename" [Sierra.Parameter.identifier (Sierra.Identifier.ref 0)] none)],
  statements := [{ libfunc_id := Sierra.Identifier.ref 2,
                   args := [],
                   branches := [{ target := none, results := [1] }] },
                 { libfunc_id := Sierra.Identifier.ref 3,
                   args := [0],
                   branches := [{ target := none, results := [0, 3] }] },
                 { libfunc_id := Sierra.Identifier.ref 1,
                   args := [3, 1],
                   branches := [{ target := none, results := [2] }] },
                 { libfunc_id := Sierra.Identifier.ref 9,
                   args := [2],
                   branches := [{ target := none, results := [2] }] },
                 { libfunc_id := Sierra.Identifier.ref 0,
                   args := [2],
                   branches := [{ target := none, results := [] }, { target := some 10, results := [4] }] },
                 { libfunc_id := Sierra.Identifier.ref 4, args := [], branches := [{ target := none, results := [] }] },
                 { libfunc_id := Sierra.Identifier.ref 5,
                   args := [0],
                   branches := [{ target := none, results := [] }] },
                 { libfunc_id := Sierra.Identifier.ref 6,
                   args := [],
                   branches := [{ target := none, results := [5] }] },
                 { libfunc_id := Sierra.Identifier.ref 9,
                   args := [5],
                   branches := [{ target := none, results := [6] }] },
                 { libfunc_id := Sierra.Identifier.ref 7,
                   args := [],
                   branches := [{ target := some 13, results := [] }] },
                 { libfunc_id := Sierra.Identifier.ref 4, args := [], branches := [{ target := none, results := [] }] },
                 { libfunc_id := Sierra.Identifier.ref 8,
                   args := [4],
                   branches := [{ target := none, results := [] }] },
                 { libfunc_id := Sierra.Identifier.ref 9,
                   args := [0],
                   branches := [{ target := none, results := [6] }] },
                 { libfunc_id := Sierra.Identifier.ref 10,
                   args := [6],
                   branches := [{ target := none, results := [7] }] },
                 { libfunc_id := Sierra.Identifier.name "return" [] none, args := [7], branches := [] }],
  declarations := [(Sierra.Identifier.ref 0, 0, [(0, Sierra.Identifier.ref 0)], [Sierra.Identifier.ref 0])] }
-/
#guard_msgs in
#eval parseGrammar code04
/--
info: fun m ref0 ρ => ref0 - ↑(Int.ofNat 5) = 0 ∧ ↑(Int.ofNat 0) = ρ ∨ ref0 - ↑(Int.ofNat 5) ≠ 0 ∧ ref0 = ρ
 Inferred Type:Sierra.Metadata → Sierra.F → Sierra.F → Prop -/
#guard_msgs in
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
/--
info: Except.ok { typedefs := [(Sierra.Identifier.ref 0, Sierra.Identifier.name "felt252" [] none)],
  libfuncs := [(Sierra.Identifier.ref 0,
                Sierra.Identifier.name "rename" [Sierra.Parameter.identifier (Sierra.Identifier.ref 0)] none),
               (Sierra.Identifier.ref 1, Sierra.Identifier.name "felt252_const" [Sierra.Parameter.const 4] none)],
  statements := [{ libfunc_id := Sierra.Identifier.ref 0,
                   args := [0],
                   branches := [{ target := none, results := [1] }] },
                 { libfunc_id := Sierra.Identifier.ref 1,
                   args := [],
                   branches := [{ target := none, results := [0] }] },
                 { libfunc_id := Sierra.Identifier.name "return" [] none, args := [1], branches := [] }],
  declarations := [(Sierra.Identifier.name "foo" [] none,
                    0,
                    [(0, Sierra.Identifier.ref 0)],
                    [Sierra.Identifier.ref 0])] } -/
#guard_msgs in
#eval parseGrammar code05
/--
info: fun m ref0 ρ => ref0 = ↑(Int.ofNat 4) ∧ ref0 = ρ
 Inferred Type:Sierra.Metadata → Sierra.F → Sierra.F → Prop -/
#guard_msgs in
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
/--
info: Except.ok { typedefs := [(Sierra.Identifier.name "felt252" [] none, Sierra.Identifier.name "felt252" [] none)],
  libfuncs := [(Sierra.Identifier.name
                  "dup"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "felt252" [] none)]
                  none,
                Sierra.Identifier.name
                  "dup"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "felt252" [] none)]
                  none),
               (Sierra.Identifier.name "felt252_add" [] none, Sierra.Identifier.name "felt252_add" [] none),
               (Sierra.Identifier.name
                  "drop"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "felt252" [] none)]
                  none,
                Sierra.Identifier.name
                  "drop"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "felt252" [] none)]
                  none),
               (Sierra.Identifier.name
                  "store_temp"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "felt252" [] none)]
                  none,
                Sierra.Identifier.name
                  "store_temp"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "felt252" [] none)]
                  none)],
  statements := [{ libfunc_id := Sierra.Identifier.name
                                   "dup"
                                   [Sierra.Parameter.identifier (Sierra.Identifier.name "felt252" [] none)]
                                   none,
                   args := [0],
                   branches := [{ target := none, results := [0, 3] }] },
                 { libfunc_id := Sierra.Identifier.name
                                   "dup"
                                   [Sierra.Parameter.identifier (Sierra.Identifier.name "felt252" [] none)]
                                   none,
                   args := [1],
                   branches := [{ target := none, results := [1, 4] }] },
                 { libfunc_id := Sierra.Identifier.name "felt252_add" [] none,
                   args := [3, 4],
                   branches := [{ target := none, results := [2] }] },
                 { libfunc_id := Sierra.Identifier.name
                                   "drop"
                                   [Sierra.Parameter.identifier (Sierra.Identifier.name "felt252" [] none)]
                                   none,
                   args := [2],
                   branches := [{ target := none, results := [] }] },
                 { libfunc_id := Sierra.Identifier.name "felt252_add" [] none,
                   args := [0, 1],
                   branches := [{ target := none, results := [5] }] },
                 { libfunc_id := Sierra.Identifier.name
                                   "store_temp"
                                   [Sierra.Parameter.identifier (Sierra.Identifier.name "felt252" [] none)]
                                   none,
                   args := [5],
                   branches := [{ target := none, results := [6] }] },
                 { libfunc_id := Sierra.Identifier.name "return" [] none, args := [6], branches := [] }],
  declarations := [(Sierra.Identifier.name "test" [] (some (Sierra.Identifier.name "foo" [] none)),
                    0,
                    [(0, Sierra.Identifier.name "felt252" [] none), (1, Sierra.Identifier.name "felt252" [] none)],
                    [Sierra.Identifier.name "felt252" [] none])] } -/
#guard_msgs in
#eval parseGrammar e2etest_felt_add
/--
info: fun m ref0 ref1 ρ => ref0 + ref1 = ρ
 Inferred Type:Sierra.Metadata → Sierra.F → Sierra.F → Sierra.F → Prop -/
#guard_msgs in
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
/--
info: Except.ok { typedefs := [(Sierra.Identifier.ref 0, Sierra.Identifier.name "felt252" [] none),
               (Sierra.Identifier.ref 1,
                Sierra.Identifier.name
                  "Enum"
                  [Sierra.Parameter.usertype (Sierra.Identifier.name "foo" [] none),
                   Sierra.Parameter.identifier (Sierra.Identifier.ref 0),
                   Sierra.Parameter.identifier (Sierra.Identifier.ref 0)]
                  none),
               (Sierra.Identifier.ref 2,
                Sierra.Identifier.name
                  "Enum"
                  [Sierra.Parameter.usertype (Sierra.Identifier.name "bar" [] none),
                   Sierra.Parameter.identifier (Sierra.Identifier.ref 1),
                   Sierra.Parameter.identifier (Sierra.Identifier.ref 1)]
                  none)],
  libfuncs := [(Sierra.Identifier.ref 0,
                Sierra.Identifier.name
                  "enum_init"
                  [Sierra.Parameter.identifier (Sierra.Identifier.ref 1), Sierra.Parameter.const 1]
                  none),
               (Sierra.Identifier.ref 1,
                Sierra.Identifier.name
                  "enum_init"
                  [Sierra.Parameter.identifier (Sierra.Identifier.ref 2), Sierra.Parameter.const 1]
                  none)],
  statements := [{ libfunc_id := Sierra.Identifier.ref 0,
                   args := [0],
                   branches := [{ target := none, results := [1] }] },
                 { libfunc_id := Sierra.Identifier.ref 1,
                   args := [1],
                   branches := [{ target := none, results := [2] }] },
                 { libfunc_id := Sierra.Identifier.name "return" [] none, args := [2], branches := [] }],
  declarations := [(Sierra.Identifier.name "foo" [] none,
                    0,
                    [(0, Sierra.Identifier.ref 0)],
                    [Sierra.Identifier.ref 2])] } -/
#guard_msgs in
#eval parseGrammar test_enum_init
/--
info: fun m ref0 ρ => Sum.inr (Sum.inr ref0) = ρ
 Inferred Type:Sierra.Metadata → Sierra.F → (Sierra.F ⊕ Sierra.F) ⊕ Sierra.F ⊕ Sierra.F → Prop -/
#guard_msgs in
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
/--
info: Except.ok { typedefs := [(Sierra.Identifier.name "F" [] none, Sierra.Identifier.name "felt252" [] none),
               (Sierra.Identifier.name "E" [] none,
                Sierra.Identifier.name
                  "Enum"
                  [Sierra.Parameter.usertype (Sierra.Identifier.name "foo" [] none),
                   Sierra.Parameter.identifier (Sierra.Identifier.name "F" [] none),
                   Sierra.Parameter.identifier (Sierra.Identifier.name "F" [] none)]
                  none)],
  libfuncs := [(Sierra.Identifier.name "init" [] none,
                Sierra.Identifier.name
                  "enum_init"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "E" [] none), Sierra.Parameter.const 1]
                  none),
               (Sierra.Identifier.name "ematch" [] none,
                Sierra.Identifier.name
                  "enum_match"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "E" [] none)]
                  none)],
  statements := [{ libfunc_id := Sierra.Identifier.name "init" [] none,
                   args := [0],
                   branches := [{ target := none, results := [1] }] },
                 { libfunc_id := Sierra.Identifier.name "ematch" [] none,
                   args := [1],
                   branches := [{ target := none, results := [2] }, { target := some 3, results := [3] }] },
                 { libfunc_id := Sierra.Identifier.name "return" [] none, args := [2], branches := [] },
                 { libfunc_id := Sierra.Identifier.name "return" [] none, args := [3], branches := [] }],
  declarations := [(Sierra.Identifier.name "foo" [] none,
                    0,
                    [(0, Sierra.Identifier.name "F" [] none)],
                    [Sierra.Identifier.name "F" [] none])] } -/
#guard_msgs in
#eval parseGrammar test_enum_match
/--
info: fun m ref0 ρ => ∃ ref2 ref3, Sum.inl ref2 = Sum.inr ref0 ∧ ref2 = ρ ∨ Sum.inr ref3 = Sum.inr ref0 ∧ ref3 = ρ
 Inferred Type:Sierra.Metadata → Sierra.F → Sierra.F → Prop -/
#guard_msgs in
#eval analyzeFile test_enum_match

def test_struct_construct :=
"type F = felt252;
type S = Struct<ut@foo, F, F>;

libfunc construct = struct_construct<S>;

construct([0], [1]) -> ([2]);
return([2]);

foo@0([0]: F, [1]: F) -> (F);"
/--
info: Except.ok { typedefs := [(Sierra.Identifier.name "F" [] none, Sierra.Identifier.name "felt252" [] none),
               (Sierra.Identifier.name "S" [] none,
                Sierra.Identifier.name
                  "Struct"
                  [Sierra.Parameter.usertype (Sierra.Identifier.name "foo" [] none),
                   Sierra.Parameter.identifier (Sierra.Identifier.name "F" [] none),
                   Sierra.Parameter.identifier (Sierra.Identifier.name "F" [] none)]
                  none)],
  libfuncs := [(Sierra.Identifier.name "construct" [] none,
                Sierra.Identifier.name
                  "struct_construct"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "S" [] none)]
                  none)],
  statements := [{ libfunc_id := Sierra.Identifier.name "construct" [] none,
                   args := [0, 1],
                   branches := [{ target := none, results := [2] }] },
                 { libfunc_id := Sierra.Identifier.name "return" [] none, args := [2], branches := [] }],
  declarations := [(Sierra.Identifier.name "foo" [] none,
                    0,
                    [(0, Sierra.Identifier.name "F" [] none), (1, Sierra.Identifier.name "F" [] none)],
                    [Sierra.Identifier.name "F" [] none])] } -/
#guard_msgs in
#eval parseGrammar test_struct_construct
/--
info: fun m ref0 ref1 ρ => (ref0, ref1) = ρ
 Inferred Type:Sierra.Metadata → Sierra.F → Sierra.F → Sierra.F → Prop -/
#guard_msgs in
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
/--
info: Except.ok { typedefs := [(Sierra.Identifier.name "F" [] none, Sierra.Identifier.name "felt252" [] none),
               (Sierra.Identifier.name "S" [] none,
                Sierra.Identifier.name
                  "Struct"
                  [Sierra.Parameter.usertype (Sierra.Identifier.name "foo" [] none),
                   Sierra.Parameter.identifier (Sierra.Identifier.name "F" [] none),
                   Sierra.Parameter.identifier (Sierra.Identifier.name "F" [] none)]
                  none)],
  libfuncs := [(Sierra.Identifier.name "construct" [] none,
                Sierra.Identifier.name
                  "struct_construct"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "S" [] none)]
                  none),
               (Sierra.Identifier.name "deconstruct" [] none,
                Sierra.Identifier.name
                  "struct_deconstruct"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "S" [] none)]
                  none)],
  statements := [{ libfunc_id := Sierra.Identifier.name "construct" [] none,
                   args := [0, 1],
                   branches := [{ target := none, results := [2] }] },
                 { libfunc_id := Sierra.Identifier.name "deconstruct" [] none,
                   args := [2],
                   branches := [{ target := none, results := [3, 4] }] },
                 { libfunc_id := Sierra.Identifier.name "return" [] none, args := [3], branches := [] }],
  declarations := [(Sierra.Identifier.name "foo" [] none,
                    0,
                    [(0, Sierra.Identifier.name "F" [] none), (1, Sierra.Identifier.name "F" [] none)],
                    [Sierra.Identifier.name "F" [] none])] } -/
#guard_msgs in
#eval parseGrammar test_struct_deconstruct
/--
info: fun m ref0 ref1 ρ => ∃ ref3 ref4, (ref3, ref4) = (ref0, ref1) ∧ ref3 = ρ
 Inferred Type:Sierra.Metadata → Sierra.F → Sierra.F → Sierra.F → Prop -/
#guard_msgs in
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
/--
info: Except.ok { typedefs := [(Sierra.Identifier.name "F" [] none, Sierra.Identifier.name "felt252" [] none),
               (Sierra.Identifier.name "S" [] none,
                Sierra.Identifier.name
                  "Struct"
                  [Sierra.Parameter.usertype (Sierra.Identifier.name "foo" [] none),
                   Sierra.Parameter.identifier (Sierra.Identifier.name "F" [] none),
                   Sierra.Parameter.identifier (Sierra.Identifier.name "F" [] none)]
                  none)],
  libfuncs := [(Sierra.Identifier.name "construct" [] none,
                Sierra.Identifier.name
                  "struct_construct"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "S" [] none)]
                  none),
               (Sierra.Identifier.name "deconstruct" [] none,
                Sierra.Identifier.name
                  "struct_deconstruct"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "S" [] none)]
                  none)],
  statements := [{ libfunc_id := Sierra.Identifier.name "construct" [] none,
                   args := [0, 0],
                   branches := [{ target := none, results := [1] }] },
                 { libfunc_id := Sierra.Identifier.name "deconstruct" [] none,
                   args := [1],
                   branches := [{ target := none, results := [2, 3] }] },
                 { libfunc_id := Sierra.Identifier.name "return" [] none, args := [0], branches := [] }],
  declarations := [(Sierra.Identifier.name "foo" [] none,
                    0,
                    [(0, Sierra.Identifier.name "F" [] none)],
                    [Sierra.Identifier.name "F" [] none])] } -/
#guard_msgs in
#eval parseGrammar test_struct_deconstruct'
/--
info: fun m ref0 ρ => ∃ ref2 ref3, (ref2, ref3) = (ref0, ref0) ∧ ref0 = ρ
 Inferred Type:Sierra.Metadata → Sierra.F → Sierra.F → Prop -/
#guard_msgs in
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
/--
info: Except.ok { typedefs := [(Sierra.Identifier.name "felt252" [] none, Sierra.Identifier.name "felt252" [] none),
               (Sierra.Identifier.name "RangeCheck" [] none, Sierra.Identifier.name "RangeCheck" [] none),
               (Sierra.Identifier.name "u128" [] none, Sierra.Identifier.name "u128" [] none),
               (Sierra.Identifier.name "Unit" [] none,
                Sierra.Identifier.name
                  "Struct"
                  [Sierra.Parameter.usertype (Sierra.Identifier.name "Tuple" [] none)]
                  none),
               (Sierra.Identifier.name
                  "core"
                  []
                  (some (Sierra.Identifier.name
                     "option"
                     []
                     (some (Sierra.Identifier.name
                        "Option"
                        [Sierra.Parameter.identifier
                           (Sierra.Identifier.name
                             "core"
                             []
                             (some (Sierra.Identifier.name
                                "integer"
                                []
                                (some (Sierra.Identifier.name "u128" [] none)))))]
                        none)))),
                Sierra.Identifier.name
                  "Enum"
                  [Sierra.Parameter.usertype
                     (Sierra.Identifier.name
                       "core"
                       []
                       (some (Sierra.Identifier.name
                          "option"
                          []
                          (some (Sierra.Identifier.name
                             "Option"
                             [Sierra.Parameter.identifier
                                (Sierra.Identifier.name
                                  "core"
                                  []
                                  (some (Sierra.Identifier.name
                                     "integer"
                                     []
                                     (some (Sierra.Identifier.name "u128" [] none)))))]
                             none))))),
                   Sierra.Parameter.identifier (Sierra.Identifier.name "u128" [] none),
                   Sierra.Parameter.identifier (Sierra.Identifier.name "Unit" [] none)]
                  none),
               (Sierra.Identifier.name
                  "Tuple"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "u128" [] none)]
                  none,
                Sierra.Identifier.name
                  "Struct"
                  [Sierra.Parameter.usertype (Sierra.Identifier.name "Tuple" [] none),
                   Sierra.Parameter.identifier (Sierra.Identifier.name "u128" [] none)]
                  none),
               (Sierra.Identifier.name
                  "Array"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "felt252" [] none)]
                  none,
                Sierra.Identifier.name
                  "Array"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "felt252" [] none)]
                  none),
               (Sierra.Identifier.name
                  "core"
                  []
                  (some (Sierra.Identifier.name
                     "PanicResult"
                     [Sierra.Parameter.tuple
                        [Sierra.Parameter.identifier
                           (Sierra.Identifier.name
                             "core"
                             []
                             (some (Sierra.Identifier.name
                                "integer"
                                []
                                (some (Sierra.Identifier.name "u128" [] none)))))]]
                     none)),
                Sierra.Identifier.name
                  "Enum"
                  [Sierra.Parameter.usertype
                     (Sierra.Identifier.name
                       "core"
                       []
                       (some (Sierra.Identifier.name
                          "PanicResult"
                          [Sierra.Parameter.tuple
                             [Sierra.Parameter.identifier
                                (Sierra.Identifier.name
                                  "core"
                                  []
                                  (some (Sierra.Identifier.name
                                     "integer"
                                     []
                                     (some (Sierra.Identifier.name "u128" [] none)))))]]
                          none))),
                   Sierra.Parameter.identifier
                     (Sierra.Identifier.name
                       "Tuple"
                       [Sierra.Parameter.identifier (Sierra.Identifier.name "u128" [] none)]
                       none),
                   Sierra.Parameter.identifier
                     (Sierra.Identifier.name
                       "Array"
                       [Sierra.Parameter.identifier (Sierra.Identifier.name "felt252" [] none)]
                       none)]
                  none)],
  libfuncs := [],
  statements := [],
  declarations := [] } -/
#guard_msgs in
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
/--
info: Except.ok { typedefs := [(Sierra.Identifier.name "F" [] none, Sierra.Identifier.name "felt252" [] none)],
  libfuncs := [(Sierra.Identifier.name "c5" [] none,
                Sierra.Identifier.name "felt252_const" [Sierra.Parameter.const 5] none),
               (Sierra.Identifier.name "call" [] none,
                Sierra.Identifier.name
                  "function_call"
                  [Sierra.Parameter.userfunc (Sierra.Identifier.name "foo" [] none)]
                  none)],
  statements := [{ libfunc_id := Sierra.Identifier.name "c5" [] none,
                   args := [],
                   branches := [{ target := none, results := [1] }] },
                 { libfunc_id := Sierra.Identifier.name "return" [] none, args := [1], branches := [] },
                 { libfunc_id := Sierra.Identifier.name "call" [] none,
                   args := [2],
                   branches := [{ target := none, results := [3] }] },
                 { libfunc_id := Sierra.Identifier.name "return" [] none, args := [3], branches := [] }],
  declarations := [(Sierra.Identifier.name "foo" [] none,
                    0,
                    [(0, Sierra.Identifier.name "F" [] none)],
                    [Sierra.Identifier.name "F" [] none]),
                   (Sierra.Identifier.name "bar" [] none,
                    2,
                    [(2, Sierra.Identifier.name "F" [] none)],
                    [Sierra.Identifier.name "F" [] none])] } -/
#guard_msgs in
#eval parseGrammar test_function_call_01
/--
info: fun m ref0 ρ => ↑(Int.ofNat 5) = ρ
 Inferred Type:Sierra.Metadata → Sierra.F → Sierra.F → Prop -/
#guard_msgs in
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
/--
info: Except.ok { typedefs := [(Sierra.Identifier.name "F" [] none, Sierra.Identifier.name "felt252" [] none)],
  libfuncs := [(Sierra.Identifier.name "c5" [] none,
                Sierra.Identifier.name "felt252_const" [Sierra.Parameter.const 5] none),
               (Sierra.Identifier.name "call_bar" [] none,
                Sierra.Identifier.name
                  "function_call"
                  [Sierra.Parameter.userfunc (Sierra.Identifier.name "bar" [] none)]
                  none)],
  statements := [{ libfunc_id := Sierra.Identifier.name "c5" [] none,
                   args := [],
                   branches := [{ target := none, results := [1] }] },
                 { libfunc_id := Sierra.Identifier.name "return" [] none, args := [1], branches := [] },
                 { libfunc_id := Sierra.Identifier.name "call_bar" [] none,
                   args := [2],
                   branches := [{ target := none, results := [3] }] },
                 { libfunc_id := Sierra.Identifier.name "return" [] none, args := [3], branches := [] }],
  declarations := [(Sierra.Identifier.name "bar" [] none,
                    0,
                    [(0, Sierra.Identifier.name "F" [] none)],
                    [Sierra.Identifier.name "F" [] none]),
                   (Sierra.Identifier.name "baz" [] none,
                    2,
                    [(2, Sierra.Identifier.name "F" [] none)],
                    [Sierra.Identifier.name "F" [] none])] } -/
#guard_msgs in
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
/--
info: Except.ok { typedefs := [(Sierra.Identifier.name "F" [] none, Sierra.Identifier.name "felt252" [] none)],
  libfuncs := [(Sierra.Identifier.name "c5" [] none,
                Sierra.Identifier.name "felt252_const" [Sierra.Parameter.const 5] none),
               (Sierra.Identifier.name "call_bar" [] none,
                Sierra.Identifier.name
                  "function_call"
                  [Sierra.Parameter.userfunc (Sierra.Identifier.name "bar[expr42]" [] none)]
                  none)],
  statements := [{ libfunc_id := Sierra.Identifier.name "c5" [] none,
                   args := [],
                   branches := [{ target := none, results := [1] }] },
                 { libfunc_id := Sierra.Identifier.name "return" [] none, args := [1], branches := [] },
                 { libfunc_id := Sierra.Identifier.name "call_bar" [] none,
                   args := [2],
                   branches := [{ target := none, results := [3] }] },
                 { libfunc_id := Sierra.Identifier.name "return" [] none, args := [3], branches := [] }],
  declarations := [(Sierra.Identifier.name "bar[expr42]" [] none,
                    0,
                    [(0, Sierra.Identifier.name "F" [] none)],
                    [Sierra.Identifier.name "F" [] none]),
                   (Sierra.Identifier.name "baz" [] none,
                    2,
                    [(2, Sierra.Identifier.name "F" [] none)],
                    [Sierra.Identifier.name "F" [] none])] } -/
#guard_msgs in
#eval parseGrammar test_square_brackets
/--
info: fun m ref0 ρ => ↑(Int.ofNat 5) = ρ
 Inferred Type:Sierra.Metadata → Sierra.F → Sierra.F → Prop -/
#guard_msgs in
#eval analyzeFile test_square_brackets

def test_end :=
"libfunc function_call<user@foo::end> = function_call<user@foo::end::bar>;"
/--
info: Except.ok { typedefs := [],
  libfuncs := [(Sierra.Identifier.name
                  "function_call"
                  [Sierra.Parameter.userfunc
                     (Sierra.Identifier.name "foo" [] (some (Sierra.Identifier.name "end" [] none)))]
                  none,
                Sierra.Identifier.name
                  "function_call"
                  [Sierra.Parameter.userfunc
                     (Sierra.Identifier.name
                       "foo"
                       []
                       (some (Sierra.Identifier.name "end" [] (some (Sierra.Identifier.name "bar" [] none)))))]
                  none)],
  statements := [],
  declarations := [] } -/
#guard_msgs in
#eval parseGrammar test_end

def test_local :=
"type F = felt252;

libfunc a = alloc_local<F>;
libfunc s = store_local<F>;

a() -> ([1]);
s([1], [0]) -> ([2]);
return([2]);

foo@0([0]: F) -> (F);"
/--
info: Except.ok { typedefs := [(Sierra.Identifier.name "F" [] none, Sierra.Identifier.name "felt252" [] none)],
  libfuncs := [(Sierra.Identifier.name "a" [] none,
                Sierra.Identifier.name
                  "alloc_local"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "F" [] none)]
                  none),
               (Sierra.Identifier.name "s" [] none,
                Sierra.Identifier.name
                  "store_local"
                  [Sierra.Parameter.identifier (Sierra.Identifier.name "F" [] none)]
                  none)],
  statements := [{ libfunc_id := Sierra.Identifier.name "a" [] none,
                   args := [],
                   branches := [{ target := none, results := [1] }] },
                 { libfunc_id := Sierra.Identifier.name "s" [] none,
                   args := [1, 0],
                   branches := [{ target := none, results := [2] }] },
                 { libfunc_id := Sierra.Identifier.name "return" [] none, args := [2], branches := [] }],
  declarations := [(Sierra.Identifier.name "foo" [] none,
                    0,
                    [(0, Sierra.Identifier.name "F" [] none)],
                    [Sierra.Identifier.name "F" [] none])] } -/
#guard_msgs in
#eval parseGrammar test_local
/--
info: fun m ref0 ρ => ref0 = ρ
 Inferred Type:Sierra.Metadata → Sierra.F → Sierra.F → Prop -/
#guard_msgs in
#eval analyzeFile test_local
