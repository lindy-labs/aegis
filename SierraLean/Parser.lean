import Megaparsec.Parsec
import Megaparsec.MonadParsec
import Megaparsec.Common
import Megaparsec.Char

open MonadParsec Megaparsec Megaparsec.Char Megaparsec.Parsec Megaparsec.Common Lean

mutual

inductive Identifier where
  | name (s : String) (ps : List Parameter) (tl : Option Identifier)
  | ref (n : Nat)
  deriving Repr, Hashable, BEq, Inhabited

inductive Parameter where
  | identifier (i : Identifier)
  | const (n : Int)
  | usertype (s : Identifier)
  | userfunc (s : Identifier)
  | libfunc (i : Identifier)
  | tuple (ps : List Parameter)
  deriving Repr, Inhabited, Hashable, BEq

-- TODO differentiate functions and types, or even better, builtin types, user types,
-- libfuncs, and user functions

end

structure BranchInfo where
  (target : Option Nat)  -- Is set to `.none` if statement is fallthrough
  (results : List Nat)
  deriving Repr, Inhabited

structure Statement where
  (libfunc_id : Identifier)
  (args : List Nat)
  (branches : List BranchInfo)
  deriving Repr, Inhabited

structure SierraFile where
  (typedefs : List (Identifier × Identifier))
  (libfuncs : List (Identifier × Identifier))
  (statements : List Statement)
  (declarations : List (Identifier × Nat × List (Nat × Identifier) × List Identifier))
  deriving Repr, Inhabited

mutual

partial def identifierToString : Identifier → String
| .name s ps tl =>
  let ps := match ps with
  | [] => "" 
  | ps@_ => "<" ++ String.intercalate ", " (parameterToString <$> ps) ++ ">"
  let hd := s ++ ps
  match tl with
  | .some i => hd ++ "::" ++ identifierToString i
  | .none => hd
| .ref n => s!"[{n}]"

partial def parameterToString : Parameter → String
| .identifier i => identifierToString i
| .const n => toString n
| .tuple ps => "(" ++ String.intercalate ", " (parameterToString <$> ps) ++ ")"
| .usertype i => "ut@" ++ identifierToString i
| .userfunc i => "user@" ++ identifierToString i
| .libfunc i => "lib@" ++ identifierToString i

end

instance : ToString Identifier where toString := identifierToString
instance : ToString Parameter where toString := parameterToString
instance : ToString Statement where toString x := toString $ repr x
instance : ToString SierraFile where toString x := toString $ repr x


abbrev P := Parsec Char String Unit  -- TODO replace the `Unit` by a proper error type

/-- Parses a natural number -/
def numP : P Nat := do return String.toNat! <| String.mk <| ← some' (satisfy Char.isDigit)

/-- Parses an integer -/
partial def intP : P Int := do
  match ← option <| discard <| single '-' with
  | .none    => numP
  | .some () => intP >>= fun x => pure <| -x

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
  let c : Char ← satisfy fun c => c.isAlpha || c == '_'
  let cs : List Char ← many' (satisfy fun c => c.isAlphanum || c == '_')
  return String.mk (c :: cs)

/-- Parses a reference to a type or memory cell -/
def refP : P Nat := between '[' ']' numP

/-- Wraps a refernce into an identifier -/
def refIdentifierP : P Identifier := .ref <$> refP

mutual

/-- Parses a name-based identifier -/
partial def nameP : P Identifier := do
  let s ← atomP
  let is ← attempt (do
    discard <| optional <| string "::"
    between '<' '>' <| sepEndBy' parameterP commaP) <|> (pure [])
  let tl ← optional (do discard <| string "::"; nameP)
  return .name s is tl

/-- Parses a reference-based identifier -/
partial def identifierP := 
  nameP
  <|> (do discard <| single '@'; nameP)
  <|> refIdentifierP

/-- Parses a parameter, i.e. a constant or an identifier -/
partial def parameterP : P Parameter :=
  (.const <$> intP)
  <|> attempt (do discard <| string "ut@"; return .usertype (← identifierP))
  <|> attempt (do discard <| string "user@"; return .userfunc (← identifierP))
  <|> attempt (do discard <| string "lib@"; return .libfunc (← identifierP))
  <|> attempt (do
    let foo ← between '(' ')' <| sepEndBy' parameterP commaP
    return .tuple foo )
  <|> (.identifier <$> identifierP)

end

/-- Parses an equality between two identifiers -/
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

/-- Parses a simple `BranchInfo` as it appears in a `{` `}` branching -/
def branchInfoP : P BranchInfo := do
  blanksP
  let t ← (do discard <| string "fallthrough"; pure Option.none)
    <|> (.some <$> numP)
  return { target := t, results := ← refTupleP }

/-- Parses a statement line -/
def statementLineP : P Statement := do
  let ident ← identifierP
  let args ← refTupleP
  blanksP
  let branches : List BranchInfo ← (do  -- Parse non-branching statmeent
      discard <| string "->"; blanksP
      return [{ target := .none, results := ← refTupleP }])
    -- Parse branching statement
    <|> (do between '{' '}' <| sepEndBy' branchInfoP blanksP)
    -- To parse the return (TODO make cleaner)
    <|> pure []
  semicolonP
  return { libfunc_id := ident, args := args, branches := branches }

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
