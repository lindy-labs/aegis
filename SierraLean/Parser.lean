import Lean.Parser
import Lean
import Mathlib.Tactic.DeriveToExpr

open Lean Parser

namespace Sierra

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

declare_syntax_cat identifier
declare_syntax_cat parameter
declare_syntax_cat branch_info
declare_syntax_cat sierra_file

syntax (("@"? ident) <|> "return") atomic("::"? "<" parameter,* ">")?  ("::" identifier)? : identifier
syntax "[" num "]" : identifier

syntax identifier : parameter
syntax atomic("-" num) : parameter
syntax num : parameter
syntax "user@" identifier : parameter
syntax "ut@" identifier : parameter
syntax "lib@" identifier : parameter
syntax "(" parameter,*,? ")" : parameter

syntax refTuple := "(" ("[" num "]"),* ")"
syntax declarationArg := "[" num "]" ":" identifier

syntax "fallthrough" refTuple : branch_info
syntax num refTuple : branch_info

syntax typedefLine := &"type" identifier "=" identifier ";"
syntax libfuncLine := "libfunc" identifier "=" identifier ";"
syntax statementLine := identifier refTuple 
  (("->" refTuple) <|> ("{" branch_info* "}"))? ";"
syntax declarationLine := identifier "@" num "(" declarationArg,* ")" "->" "(" identifier,* ")" ";"

syntax typedefLine* libfuncLine* atomic(statementLine)* declarationLine* : sierra_file

mutual

partial def elabIdentifier : Syntax → Except String Identifier
| `(identifier|$[@]? $i:ident $[$[::]? <$ps,*>]? $[:: $tl:identifier]?) => do
  let i := i.getId.toString
  let ps := (← ps.mapM fun ps => ps.getElems.mapM elabParameter).getD #[]
  let tl ← tl.mapM elabIdentifier
  .ok <| .name i ps.toList tl
| `(identifier|return) => .ok <| .name "return" [] .none
| `(identifier|[$n:num]) => .ok <| .ref n.getNat
| _ => .error "Could not elab identifier"

partial def elabParameter : TSyntax `parameter → Except String Parameter
| `(parameter|-$n:num) => .ok <| .const <| -n.getNat
| `(parameter|user@$i) => do
  let i ← elabIdentifier i
  .ok <| .userfunc i
| `(parameter|ut@$i) => do
  let i ← elabIdentifier i
  .ok <| .usertype i
| `(parameter|lib@$i) => do
  let i ← elabIdentifier i
  .ok <| .libfunc i
| `(parameter|$n:num) => .ok <| .const <| n.getNat
| `(parameter|$i:identifier) => do
  let i ← elabIdentifier i
  .ok <| .identifier i
| `(parameter|($ps:parameter,*)) => do
  let ps ← ps.getElems.mapM elabParameter
  .ok <| .tuple ps.toList
| _ => .error "Could not elab parameter"

end

def elabBranchInfo : TSyntax `branch_info → Except String BranchInfo
| `(branch_info|fallthrough($[[$rs]],*)) =>
  .ok { target := .none, results := (rs.map TSyntax.getNat).toList }
| `(branch_info|$t:num($[[$rs]],*)) =>
  .ok { target := .some t.getNat, results := (rs.map TSyntax.getNat).toList }
| _ => .error "Could not elab branch info"

def elabStatementLine : TSyntax `Sierra.statementLine → Except String Statement
| `(statementLine|return($[[$args]],*);) => do
  .ok { libfunc_id := .name "return" [] none, args := (args.map (·.getNat)).toList, branches := [] }
| `(statementLine|$i:identifier($[[$args]],*) -> ($[[$ress]],*);) => do
  let i ← elabIdentifier i
  .ok { libfunc_id := i, args := (args.map (·.getNat)).toList,
        branches := [{ target := .none, results := (ress.map (·.getNat)).toList }] }
| `(statementLine|$i:identifier($[[$args]],*) $[{ $bs* }]?;) => do
  let i ← elabIdentifier i
  let bs := bs.getD #[]
  let b ← (bs.mapM elabBranchInfo)
  .ok { libfunc_id := i, args := (args.map (·.getNat)).toList, branches := b.toList }
| `(statementLine|$i:identifier($[[$args]],*);) => do
  let i ← elabIdentifier i
  .ok { libfunc_id := i, args := (args.map (·.getNat)).toList, branches := [] }
| x => .error s!"Could not elab statement {x}"

def elabDeclarationArg : TSyntax `Sierra.declarationArg → Except String (Nat × Identifier)
| `(declarationArg|[$n:num]:$i) => do .ok <| (n.getNat, ← elabIdentifier i)
| _ => .error "Could not elab declaration argument"

def elabDeclarationLine : TSyntax `Sierra.declarationLine →
    Except String (Identifier × Nat × List (Nat × Identifier) × List Identifier)
| `(declarationLine|$i:identifier@$n($args,*) -> ($rets,*);) => do
  let i ← elabIdentifier i
  let rets ← rets.getElems.mapM elabIdentifier
  let args ← args.getElems.mapM elabDeclarationArg
  .ok (i, n.getNat, args.toList, rets.toList)
| _ => .error "Could not elab declaration"

def elabSierraFile : Syntax → Except String SierraFile
| `(sierra_file|$[type $tlhs = $trhs;]* $[libfunc $llhs = $lrhs;]*  $sts:statementLine*
    $ds:declarationLine*) => do
  let ts := (← tlhs.mapM elabIdentifier).zip <| ← trhs.mapM elabIdentifier
  let ls := (← llhs.mapM elabIdentifier).zip <| ← lrhs.mapM elabIdentifier
  let sts := (← sts.mapM elabStatementLine).toList
  let ds := (← ds.mapM elabDeclarationLine).toList
  .ok { typedefs := ts.toList, libfuncs := ls.toList, statements := sts, declarations := ds }
| _ => .error "Could not elab Sierra file"

-- TODO solve this in a better way
def replaceNaughtyBrackets (s : String) : String :=
  (s.replace ">" "> ").replace "<" " <"

def parseGrammar (input : String) : CoreM (Except String SierraFile) := do
  let env ← getEnv
  let input := replaceNaughtyBrackets input
  pure do elabSierraFile (← runParserCategory env `sierra_file input)

def parseIdentifier (input : String) : CoreM (Except String Identifier) := do
  let env ← getEnv
  let input := replaceNaughtyBrackets input
  pure do elabIdentifier (← runParserCategory env `identifier input)
