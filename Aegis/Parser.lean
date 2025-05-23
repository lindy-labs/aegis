import Lean.Parser
import Lean
import Mathlib.Tactic.ToExpr

open Lean Parser

namespace Sierra

mutual

inductive Identifier where
  | name (s : String) (ps : List Parameter) (tl : Option Identifier)
  | ref (n : Nat)
  deriving Repr, Hashable, BEq, Inhabited, ToExpr

inductive Parameter where
  | identifier (i : Identifier)
  | const (n : Int)
  | usertype (s : Identifier)
  | userfunc (s : Identifier)
  | libfunc (i : Identifier)
  | tuple (ps : List Parameter)
  | placeholder
  deriving Repr, Inhabited, Hashable, BEq, ToExpr

end

structure BranchInfo where
  (target : Option (Nat ⊕ Identifier))  -- Is set to `.none` if statement is fallthrough
  (results : List Nat)
  deriving Repr, Inhabited

structure Statement where
  (label : Option Identifier)
  (libfunc_id : Identifier)
  (args : List Nat)
  (branches : List BranchInfo)
  deriving Repr, Inhabited

structure SierraFile where
  (typedefs : List (Identifier × Identifier))
  (libfuncs : List (Identifier × Identifier))
  (statements : List Statement)
  (declarations : List (Identifier × (Nat ⊕ Identifier) × List (Nat × Identifier) × List Identifier))
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
| .placeholder => "_"

end

instance : ToString Identifier where toString := identifierToString
instance : ToString Parameter where toString := parameterToString
instance : ToString Statement where toString x := toString $ repr x
instance : ToString SierraFile where toString x := toString $ repr x

declare_syntax_cat atom
declare_syntax_cat identifier
declare_syntax_cat parameter
declare_syntax_cat branch_info
declare_syntax_cat statement_lhs
declare_syntax_cat sierra_file

syntax "@"? ident : atom
syntax "return" : atom
syntax "end" : atom

syntax atom ("[" ident "]")? atomic("::"? "<" parameter,* ">")?  ("::" identifier)? : identifier
syntax "[" num "]" : identifier

syntax "_" : parameter
syntax "-" num : parameter
syntax num : parameter
syntax "user@" identifier : parameter
syntax "ut@" identifier : parameter
syntax "lib@" identifier : parameter
syntax "(" parameter,*,? ")" : parameter
syntax identifier : parameter

syntax boolLit := "false" <|> "true"
syntax typeInfo := "[storable:" boolLit "," "drop:" boolLit "," "dup:" boolLit "," "zero_sized:" boolLit "]"

syntax stmtLoc := num <|> identifier

syntax refTuple := "(" ("[" num "]"),* ")"
syntax declarationArg := "[" num "]" ":" identifier

syntax "fallthrough" refTuple : branch_info
syntax stmtLoc refTuple : branch_info

syntax "->" refTuple : statement_lhs
syntax "{" branch_info* "}" : statement_lhs

syntax typedefLine := &"type" identifier "=" identifier (typeInfo)? ";" ("//" num)?
syntax libfuncLine := "libfunc" identifier "=" identifier ";"  ("//" num)?
syntax statementLine := atomic(identifier noWs ":")? identifier refTuple (statement_lhs)? ";"  ("//" num)?
syntax declarationLine := identifier "@" (num <|> identifier) "(" declarationArg,* ")" "->" "(" identifier,* ")" ";"  ("//" num)?

syntax typedefLine* libfuncLine* atomic(statementLine)* declarationLine* : sierra_file

mutual

private partial def elabIdentifierAux (i : String) (j: Option (TSyntax `ident))
    (ps : Option (Syntax.TSepArray `parameter ",")) (tl: Option (TSyntax `identifier)) :
    Except String Identifier := do
  let j := (j.map ("[" ++ ·.getId.toString ++ "]")).getD ""
  let i := i ++ j
  let ps := (← ps.mapM fun ps => ps.getElems.mapM elabParameter).getD #[]
  let tl ← tl.mapM elabIdentifier
  .ok <| .name i ps.toList tl

partial def elabIdentifier : Syntax → Except String Identifier
| `(identifier|$[@]? $i:ident $[[$j:ident]]? $[$[::]? <$ps,*>]? $[:: $tl:identifier]?) => do
  elabIdentifierAux i.getId.toString j ps tl
| `(identifier|end $[[$j:ident]]? $[$[::]? <$ps,*>]? $[:: $tl:identifier]?) => do
  elabIdentifierAux "end" j ps tl
| `(identifier|return) => .ok <| .name "return" [] .none
| `(identifier|[$n:num]) => .ok <| .ref n.getNat
| _ => .error "Could not elab identifier"

partial def elabParameter : TSyntax `parameter → Except String Parameter
| `(parameter|_) => .ok .placeholder
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
  .ok { target := .none
        results := (rs.map TSyntax.getNat).toList }
| `(branch_info|$t:num($[[$rs]],*)) =>
  .ok { target := .some (.inl t.getNat)
        results := (rs.map TSyntax.getNat).toList }
| `(branch_info|$t:identifier($[[$rs]],*)) => do
  .ok { target := .some (.inr (← elabIdentifier t))
        results := (rs.map TSyntax.getNat).toList }
| _ => .error "Could not elab branch info"

def elabStmtLoc : Option (TSyntax `identifier) → Except String (Option Identifier)
| .none => .ok .none
| .some stx =>  do .ok <| .some <| ← elabIdentifier stx

def elabStatementLine : TSyntax `Sierra.statementLine → Except String Statement
| `(statementLine|$[$loc:identifier:]? return($[[$args]],*); $[//$n]?) => do
  .ok { label := ← elabStmtLoc loc
        libfunc_id := .name "return" [] none
        args := (args.map (·.getNat)).toList
        branches := [] }
| `(statementLine|$[$loc:identifier:]? $i:identifier($[[$args]],*) -> ($[[$ress]],*); $[//$n]?) => do
  .ok { label := ← elabStmtLoc loc
        libfunc_id := ← elabIdentifier i
        args := (args.map (·.getNat)).toList
        branches := [{ target := .none, results := (ress.map (·.getNat)).toList }] }
| `(statementLine|$[$loc:identifier:]? $i:identifier($[[$args]],*) $[{ $bs* }]?; $[//$n]?) => do
  let bs := bs.getD #[]
  let b ← (bs.mapM elabBranchInfo)
  .ok { label := ← elabStmtLoc loc
        libfunc_id := ← elabIdentifier i
        args := (args.map (·.getNat)).toList
        branches := b.toList }
| `(statementLine|$[$loc:identifier:]? $i:identifier($[[$args]],*); $[//$n]?) => do
  .ok { label := ← elabStmtLoc loc
        libfunc_id := ← elabIdentifier i
        args := (args.map (·.getNat)).toList,
        branches := [] }
| x => .error s!"Could not elab statement {x}"

def elabDeclarationArg : TSyntax `Sierra.declarationArg → Except String (Nat × Identifier)
| `(declarationArg|[$n:num]:$i) => do .ok <| (n.getNat, ← elabIdentifier i)
| _ => .error "Could not elab declaration argument"

def elabDeclarationLine : TSyntax `Sierra.declarationLine →
    Except String (Identifier × (Nat ⊕ Identifier) × List (Nat × Identifier) × List Identifier)
| `(declarationLine|$i:identifier@$n:num($args,*) -> ($rets,*); $[//$n]?) => do
  let i ← elabIdentifier i
  let rets ← rets.getElems.mapM elabIdentifier
  let args ← args.getElems.mapM elabDeclarationArg
  .ok (i, .inl n.getNat, args.toList, rets.toList)
| `(declarationLine|$i:identifier@$n:identifier($args,*) -> ($rets,*); $[//$n]?) => do
  let i ← elabIdentifier i
  let rets ← rets.getElems.mapM elabIdentifier
  let args ← args.getElems.mapM elabDeclarationArg
  .ok (i, .inr (← elabIdentifier n), args.toList, rets.toList)
| _ => .error "Could not elab declaration"

def elabTypedefLine : TSyntax `Sierra.typedefLine → Except String (Identifier × Identifier)
| `(typedefLine|type $tlhs = $trhs $[[storable: $_, drop: $_, dup: $_, zero_sized: $_]]?; $[//$_]?) => do
  let tlhs ← elabIdentifier tlhs
  let trhs ← elabIdentifier trhs
  .ok (tlhs, trhs)
| _ => .error "Could not elab type definition"

def elabSierraFile : Syntax → Except String SierraFile
| `(sierra_file|$ts:typedefLine* $[libfunc $llhs = $lrhs; $[//$n]?]*  $sts:statementLine*
    $ds:declarationLine*) => do
  let ts ← ts.mapM elabTypedefLine
  let ls := (← llhs.mapM elabIdentifier).zip <| ← lrhs.mapM elabIdentifier
  let sts := (← sts.mapM elabStatementLine).toList
  let ds := (← ds.mapM elabDeclarationLine).toList
  .ok { typedefs := ts.toList, libfuncs := ls.toList, statements := sts, declarations := ds }
| _ => .error "Could not elab Sierra file"

-- TODO solve this in a better way
def replaceNaughtyBrackets (s : String) : String :=
  (((s.replace ">" "> ").replace "<" " <").replace "<-" "< -").replace "<i" "< i"

def parseGrammar (input : String) : CoreM (Except String SierraFile) := do
  let env ← getEnv
  let input := replaceNaughtyBrackets input
  pure do
    let stx ← runParserCategory env `sierra_file input
    elabSierraFile stx

def parseIdentifier (input : String) : CoreM (Except String Identifier) := do
  let env ← getEnv
  let input := replaceNaughtyBrackets input
  pure do elabIdentifier (← runParserCategory env `identifier input)
