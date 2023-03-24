import Megaparsec

open Megaparsec Parsec Common

inductive Identifier where
  | atom (s : String) (is : List Identifier)
  | ns (s : String) (i : Identifier)
  deriving Repr

-- TODO add `Nat` constants inside the pointy brackets

instance : ToString Identifier where
  toString x := toString $ repr x

abbrev P := Parsec Char String Unit  -- TODO replace the `Unit` by a proper error type

def atomP : P String := do
  let c : Char ← satisfy Char.isAlpha
  let cs : List Char ← many' (satisfy fun c => c.isAlphanum || c == '_')
  return String.mk (c :: cs)

mutual

partial def atomIdentifierP : P Identifier := do
  return .atom (← atomP) []

partial def nsIdentifierP : P Identifier := do
  let ns ← atomP
  discard (string "::")
  let i ← identifierP
  return .ns ns i

partial def identifierP : P Identifier :=
  nsIdentifierP <|> atomIdentifierP

end

def parseGrammar (code : String) : Except String Identifier :=
  Except.mapError toString $ parse identifierP code

def code := "felt252_do::foo"

#eval parseGrammar code