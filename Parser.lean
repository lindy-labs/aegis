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

-- Discard a single `,`
def commaP : P Unit := discard (single ',')

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

def parseGrammar (code : String) : Except String Identifier :=
  Except.mapError toString $ parse identifierP code

def code := "felt252_do::foo<[15]>"

#eval parseGrammar code