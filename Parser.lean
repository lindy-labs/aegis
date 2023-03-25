import Megaparsec.Parsec
import Megaparsec.MonadParsec
import Megaparsec.Common
import Megaparsec.Char

open MonadParsec Megaparsec.Char Megaparsec.Parsec

namespace Megaparsec.Common

-- TODO fix this
-- TODO make this universe polymorphic
partial def manyAttempts {m : Type → Type v} {℘ α E β : Type}
    [MonadParsec m ℘ α E β] [Monad m] [Alternative m] {γ : Type} (a : m γ) : 
    m (List γ) := do
  match ← @option m ℘ α E β γ _ _ _ a with
  | .some x => return x :: (← @manyAttempts m ℘ α E β _ _ _ γ a)
  | _       => return []

namespace Sierra

inductive Identifier where
  | name (s : String) (is : List Identifier)
  | ref (n : Nat)
  deriving Repr
-- TODO add `Nat` (and other?) constants inside the pointy brackets

instance : ToString Identifier where toString x := toString $ repr x

structure SierraFile where
  (typedefs : List (Identifier × Identifier))
  (statements : List (Identifier × List Nat × List Nat))
  (declarations : List (Identifier × Nat × List (Nat × Identifier) × List Identifier))
  deriving Repr
-- TODO add a better printer

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
def semicolonP : P Unit := discard (single ';')

/-- The name is maybe a bit misleading, this parses a whole identifier, including namespace ids -/
def atomP : P String := do
  let c : Char ← satisfy Char.isAlpha
  let cs : List Char ← many' (satisfy fun c => c.isAlphanum || c == '_' || c == ':')
  return String.mk (c :: cs)

/-- Parses a reference to a type or memory cell -/
def refP : P Nat := between '[' ']' numP

/-- Wraps a refernce into an identifier -/
def refIdentifierP : P Identifier := do return .ref (← refP)

mutual

/-- Parses a name-based identifier -/
partial def nameP : P Identifier := do
  blanksP
  let s ← atomP
  let is ← (between '<' '>' <| sepEndBy' identifierP commaP) <|> (pure [])
  return .name s is

/-- Parses a reference-based identifier -/
partial def identifierP := nameP <|> refIdentifierP

end

/-- Parses a type definition line -/
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

/-- Parses tuples of references, as in `([0], [1])` -/
def refTupleP : P (List Nat) := between '(' ')' <| sepEndBy' refP commaP

/-- Parses a statement line -/
def statementLineP : P (Identifier × List Nat × List Nat) := do
  let ident ← identifierP
  let args ← refTupleP
  blanksP
  discard <| string "->"
  blanksP
  let rets ← refTupleP
  semicolonP
  return (ident, args, rets)

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
def declarationArgListP : P (List (Nat × Identifier)) :=
  between '(' ')' <| sepEndBy' declarationArgP commaP

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

set_option pp.universes true
def sierraFileP : P SierraFile := do
  blanksP
  let typedefs ← many' (attempt typedefLineP)
  blanksP
  let statements ← many' (attempt statementLineP)
  blanksP
  let declarations ← many' declarationLineP
  blanksP
  return ⟨typedefs, statements, declarations⟩

def parseGrammar (code : String) : Except String SierraFile :=
  Except.mapError toString $ parse sierraFileP code

def code := "call_this_shit([25]) -> ([25]); call_this_shit([25]) -> ([25]); foo@42([1]: felt) -> ([2], [3]);" -- foo@42([1]: felt) -> ([2], [3]);

#eval parseGrammar code
