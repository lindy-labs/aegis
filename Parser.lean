import Megaparsec
import Megaparsec.Char

open Megaparsec Parsec Common Char

inductive Identifier where
  | name (s : String) (is : List Identifier)
  | ref (n : Nat)
  deriving Repr
-- TODO add `Nat` constants inside the pointy brackets

instance : ToString Identifier where
  toString x := toString $ repr x

abbrev P := Parsec Char String Unit  -- TODO replace the `Unit` by a proper error type

-- Parses a number
def numP : P Nat := do return String.toNat! <| String.mk <| ← some' (satisfy Char.isDigit)

-- Discard whitespace and line breaks
def blanksP : P Unit := discard $ many' (satisfy <| ([' ', '\n', '\t'].contains ·))

-- Discard a single `,` and blanks
def commaP : P Unit := do
  blanksP
  discard (single ',')
  blanksP

-- Discard a single `;`
def semicolonP : P Unit := discard (single ';')

-- The name is maybe a bit misleading, this parses a whole identifier, including namespace ids
def atomP : P String := do
  let c : Char ← satisfy Char.isAlpha
  let cs : List Char ← many' (satisfy fun c => c.isAlphanum || c == '_' || c == ':')
  return String.mk (c :: cs)

def refP : P Nat := between '[' ']' numP

def refIdentifierP : P Identifier := do return .ref (← refP)

mutual

partial def nameP : P Identifier := do
  blanksP
  let s ← atomP
  let is ← (between '<' '>' <| sepEndBy' identifierP commaP) <|> (pure [])
  return .name s is

partial def identifierP := nameP <|> refIdentifierP

end

-- Parses a type definition line
def typedefLineP : P (Identifier × Identifier) := do
  discard <| string "type "
  blanksP
  let lhs ← identifierP
  blanksP
  discard <| single '='
  blanksP
  let rhs ← nameP
  semicolonP
  return (lhs, rhs)

-- Parses tuples of references, as in `([0], [1])`
def refTupleP : P (List Nat) := between '(' ')' <| sepEndBy' refP commaP

def statementLineP : P (Identifier × List Nat × List Nat) := do
  let ident ← identifierP
  let args ← refTupleP
  blanksP
  discard <| string "->"
  blanksP
  let rets ← refTupleP
  return (ident, args, rets)

def parseGrammar (code : String) : Except String (Identifier × List Nat × List Nat) :=
  Except.mapError toString $ parse statementLineP code

def code := "foo([1]) -> ([2], [3]);"

#eval parseGrammar code