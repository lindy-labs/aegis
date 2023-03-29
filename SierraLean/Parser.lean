import Megaparsec.Parsec
import Megaparsec.MonadParsec
import Megaparsec.Common
import Megaparsec.Char

open MonadParsec Megaparsec Megaparsec.Char Megaparsec.Parsec Megaparsec.Common

mutual

inductive Identifier where
  | name (s : String) (is : List Parameter)
  | ref (n : Nat)
  deriving Repr, Hashable, BEq

inductive Parameter where  -- find out what the stuff in the pointy brackets is called
  | identifier (i : Identifier)
  | const (n : Nat)
  | usertype (i : Identifier)
  | userfunc (i : Identifier)
  | libfunc (i : Identifier)
  deriving Repr

-- TODO differentiate functions and types, or even better, builtin types, user types,
-- libfuncs, and user functions

end

structure SierraFile where
  (typedefs : List (Identifier × Identifier))
  (libfuncs : List (Identifier × Identifier))
  (statements : List (Identifier × List Nat × List Nat))
  (declarations : List (Identifier × Nat × List (Nat × Identifier) × List Identifier))
  deriving Repr

-- TODO add a better printer
instance : ToString Identifier where toString x := toString $ repr x
instance : ToString Parameter where toString x := toString $ repr x
instance : ToString SierraFile where toString x := toString $ repr x

abbrev P := Parsec Char String Unit  -- TODO replace the `Unit` by a proper error type

/-- Parses a number -/
def numP : P Nat := do return String.toNat! <| String.mk <| ← some' (satisfy Char.isDigit)

/-- Discard whitespace and line breaks -/
def blanksP : P Unit := discard $ many' (satisfy <| ([' ', '\n', '\t'].contains ·))

-- Discard a single `,` and blanks
def commaP : P Unit := do
  blanksP
  discard (single ',')
  blanksP

/-- Discard a single `;` -/
def semicolonP : P Unit := discard (single ';') *> blanksP

/-- The name is maybe a bit misleading, this parses a whole identifier, including namespace ids -/
def atomP : P String := do
  let c : Char ← satisfy Char.isAlpha
  let cs : List Char ← many' (satisfy fun c => c.isAlphanum || c == '_' || c == ':')
  return String.mk (c :: cs)

/-- Parses a reference to a type or memory cell -/
def refP : P Nat := between '[' ']' numP

/-- Wraps a refernce into an identifier -/
def refIdentifierP : P Identifier := .ref <$> refP

mutual

/-- Parses a name-based identifier -/
partial def nameP : P Identifier := do
  blanksP
  let s ← atomP
  let is ← (between '<' '>' <| sepEndBy' parameterP commaP) <|> (pure [])
  return .name s is

/-- Parses a reference-based identifier -/
partial def identifierP := nameP <|> refIdentifierP

/-- Parses a parameter, i.e. a constant or an identifier -/
partial def parameterP : P Parameter :=
  (.const <$> numP)
  <|> attempt (do discard <| string "ut@"; return .usertype (← identifierP))
  <|> attempt (do discard <| string "user@"; return .userfunc (← identifierP))
  <|> attempt (do discard <| string "lib@"; return .libfunc (← identifierP))
  <|> (.identifier <$> identifierP)

end

def identifierEqualityP : P (Identifier × Identifier) := do
  let lhs ← identifierP
  blanksP
  discard <| single '='
  blanksP
  let rhs ← nameP
  semicolonP
  return (lhs, rhs)

/-- Parses a type definition line -/
def typedefLineP : P (Identifier × Identifier) := do
  discard <| string "type "
  blanksP
  identifierEqualityP

/-- Parses a libfunc reference line -/
def libfuncLineP : P (Identifier × Identifier) := do
  discard <| string "libfunc "
  blanksP
  identifierEqualityP

/-- Parses tuples of references, as in `([0], [1])` -/
def refTupleP : P (List Nat) := between '(' ')' <| sepEndBy' refP commaP

/-- Parses a statement line -/
def statementLineP : P (Identifier × List Nat × List Nat) := do
  let ident ← identifierP
  let args ← refTupleP
  let rets? ← option (do 
    blanksP
    discard <| string "->"
    blanksP
    refTupleP)
  semicolonP
  return (ident, args, rets?.getD [])

/-- Parses a tuple of identifiers -/
def identifierTupleP : P (List Identifier) := between '(' ')' <| sepEndBy' identifierP commaP

/-- Parses a single declaration argument, containing argument position and type -/
def declarationArgP : P (Nat × Identifier) := do
  let n ← refP
  blanksP
  discard <| single ':'
  blanksP
  let ident ← identifierP
  return (n, ident)

/-- Parses a list of declaration arguments -/
def declarationArgListP := between '(' ')' <| sepEndBy' declarationArgP commaP

/-- Parses a function declaration line -/
def declarationLineP : P (Identifier × Nat × List (Nat × Identifier) × List Identifier) := do
  let ident ← identifierP
  discard <| single '@'
  let n ← numP
  let args ← declarationArgListP
  blanksP
  discard <| string "->"
  blanksP
  let retTypes ← identifierTupleP
  semicolonP
  return (ident, n, args, retTypes)

/-- Parses a Sierra file -/
def sierraFileP : P SierraFile := do
  blanksP
  let typedefs ← many' (attempt typedefLineP)
  blanksP
  let libfuncs ← many' (attempt libfuncLineP)
  blanksP
  let statements ← many' (attempt statementLineP)
  blanksP
  let declarations ← many' declarationLineP
  blanksP
  return ⟨typedefs, libfuncs, statements, declarations⟩

def parseGrammar (code : String) : Except String SierraFile :=
  Except.mapError toString $ parse sierraFileP code

def code := "
type core::option::Option::<core::integer::u128> = Enum<ut@core::option::Option::<core::integer::u128>, u128, Unit>;
type Tuple<u128> = Struct<ut@Tuple, u128>;
type Tuple<wad_ray::wad_ray::Wad> = Struct<ut@Tuple, wad_ray::wad_ray::Wad>;
type wad_ray::wad_ray::Ray = Struct<ut@wad_ray::wad_ray::Ray, u128>;
type Tuple<wad_ray::wad_ray::Ray> = Struct<ut@Tuple, wad_ray::wad_ray::Ray>;
type Tuple<u128, u128> = Struct<ut@Tuple, u128, u128>;
"  -- TODO any bigger than this and we run out of stack space, not sure what to do about it
#eval parseGrammar code

def code' := "type [0] = felt252;

libfunc [0] = felt252_const<0>;
libfunc [1] = store_temp<[0]>;

[0]() -> ([0]);
[1]([0]) -> ([1]);
return([1]);

[0]@0() -> ([0]);
"
#eval parseGrammar code'
