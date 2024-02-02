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
  deriving Repr, Inhabited, Hashable, BEq, ToExpr

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

syntax "-" num : parameter
syntax num : parameter
syntax "user@" identifier : parameter
syntax "ut@" identifier : parameter
syntax "lib@" identifier : parameter
syntax "(" parameter,*,? ")" : parameter
syntax identifier : parameter

syntax boolLit := "false" <|> "true"
syntax typeInfo := "[storable:" boolLit ", drop:" boolLit ", dup:" boolLit ", zero_sized:" boolLit "]"


syntax refTuple := "(" ("[" num "]"),* ")"
syntax declarationArg := "[" num "]" ":" identifier

syntax "fallthrough" refTuple : branch_info
syntax num refTuple : branch_info

syntax "->" refTuple : statement_lhs
syntax "{" branch_info* "}" : statement_lhs

syntax typedefLine := &"type" identifier "=" identifier (typeInfo)? ";" ("//" num)?
syntax libfuncLine := "libfunc" identifier "=" identifier ";"  ("//" num)?
syntax statementLine := identifier refTuple (statement_lhs)? ";"  ("//" num)?
syntax declarationLine := identifier "@" num "(" declarationArg,* ")" "->" "(" identifier,* ")" ";"  ("//" num)?

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
| `(statementLine|return($[[$args]],*); $[//$n]?) => do
  .ok { libfunc_id := .name "return" [] none, args := (args.map (·.getNat)).toList, branches := [] }
| `(statementLine|$i:identifier($[[$args]],*) -> ($[[$ress]],*); $[//$n]?) => do
  let i ← elabIdentifier i
  .ok { libfunc_id := i, args := (args.map (·.getNat)).toList,
        branches := [{ target := .none, results := (ress.map (·.getNat)).toList }] }
| `(statementLine|$i:identifier($[[$args]],*) $[{ $bs* }]?; $[//$n]?) => do
  let i ← elabIdentifier i
  let bs := bs.getD #[]
  let b ← (bs.mapM elabBranchInfo)
  .ok { libfunc_id := i, args := (args.map (·.getNat)).toList, branches := b.toList }
| `(statementLine|$i:identifier($[[$args]],*); $[//$n]?) => do
  let i ← elabIdentifier i
  .ok { libfunc_id := i, args := (args.map (·.getNat)).toList, branches := [] }
| x => .error s!"Could not elab statement {x}"

def elabDeclarationArg : TSyntax `Sierra.declarationArg → Except String (Nat × Identifier)
| `(declarationArg|[$n:num]:$i) => do .ok <| (n.getNat, ← elabIdentifier i)
| _ => .error "Could not elab declaration argument"

def elabDeclarationLine : TSyntax `Sierra.declarationLine →
    Except String (Identifier × Nat × List (Nat × Identifier) × List Identifier)
| `(declarationLine|$i:identifier@$n($args,*) -> ($rets,*); $[//$n]?) => do
  let i ← elabIdentifier i
  let rets ← rets.getElems.mapM elabIdentifier
  let args ← args.getElems.mapM elabDeclarationArg
  .ok (i, n.getNat, args.toList, rets.toList)
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
  ((s.replace ">" "> ").replace "<" " <").replace "<-" "< -"

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

/- JSON Parsers -/

def parseJsonArg (j : Lean.Json) : CoreM Parameter := do
  if let .ok (.arr v) := j.getObjVal? "Value" then
    if let .some (.num ⟨i, 0⟩) := v.toList.head? then
      return .const i
  if let .ok t := j.getObjVal? "Type" then
    if let .ok (.str t) := t.getObjVal? "debug_name" then
      let .ok t ← parseIdentifier t
        | throwError "unable to parse identifier in generic arguments"
      return .identifier t
  throwError "unable to parse generig arguments"

def parseJsonLongId (j : Lean.Json) : CoreM Identifier := do
  let .ok (.str gid) := j.getObjVal? "generic_id"
    | throwError "def rhs must contain generic_id"
  let .ok (.arr args) := j.getObjVal? "generic_args"
    | throwError "def rhs must contain array of generic args"
  let args ← args.mapM parseJsonArg
  pure <| .name gid args.toList .none

def parseJsonDef (j : Lean.Json) : CoreM (Identifier × Identifier) := do
  let .ok lhs := j.getObjVal? "id"
    | throwError "typedef must include id"
  let .ok (.str lhs) := lhs.getObjVal? "debug_name"
    | throwError "dbug_name must be a string!"
  let .ok lhs ← parseIdentifier lhs
    | throwError "cannot parse lhs identifier of type def"
  let .ok rhs := j.getObjVal? "long_id"
    | throwError "typedef must include long_id"
  let rhs ← parseJsonLongId rhs
  pure (lhs, rhs)

def parseJsonReturn (j : Lean.Json) : CoreM Statement := do
  let .ok (.arr ids) := j.getObjVal? "Return"
    | throwError "return must include an arrow of ids"
  let .ok ids := ids.mapM (·.getObjVal? "id")
    | throwError "return ids must include field id"
  let .ok ids := ids.mapM Json.getNum?
    | throwError "id of all ids must be a number"
  let ids ← ids.mapM fun s =>
    match s with
    | ⟨.ofNat n,0⟩ => pure n
    | _ => throwError "id of all ids must be positive integer"
  pure { libfunc_id := (.name "return" [] .none), args := ids.toList, branches := [] }

def parseJsonBranch (j : Lean.Json) : CoreM BranchInfo := do
  let .ok target := j.getObjVal? "target"
    | throwError "branch must contain target"
  let target ← match target, target.getObjVal? "Statement" with
    | .str "Fallthrough", _       => pure .none
    | _, .ok (.num ⟨.ofNat n, 0⟩) => pure <| .some n
    | _, _ =>  throwError "branch must be either Fallthrough or Statement"
  let .ok (.arr results) := j.getObjVal? "results"
    | throwError "branch must contain results"
  let results ← results.mapM fun r => do
    let .ok (.num ⟨.ofNat r, 0⟩) := r.getObjVal? "id"
      | throwError "result must contain id"
    pure r
  pure { target := target, results := results.toList }

def parseJsonInvocation (j : Lean.Json) : CoreM Statement := do
  let .ok inv := j.getObjVal? "Invocation"
    | throwError "invocation must include field Invocation"
  let .ok libfunc_id := inv.getObjVal? "libfunc_id"
    | throwError "invocation must include libfunc_id"
  let .ok (.str libfunc_id) := libfunc_id.getObjVal? "debug_name"
    | throwError "libfunc_id must include debug_name"
  let .ok libfunc_id ← parseIdentifier libfunc_id
    | throwError "failed to parse libfunc_id identifier"
  let .ok (.arr args) := inv.getObjVal? "args"
    | throwError "invocation must contain array of args"
  let .ok args := args.mapM ((·.getObjVal? "id"))
    | throwError "args must contain id"
  let args ← args.mapM fun j =>
    match j with
    | .num ⟨.ofNat n, 0⟩ => pure n
    | _ => throwError "ids must be postivie integers"
  let .ok (.arr branches) := inv.getObjVal? "branches"
    | throwError "invocation must include array of branches"
  let branches ← branches.mapM parseJsonBranch
  pure { libfunc_id := libfunc_id, args := args.toList, branches := branches.toList }

def parseJsonStatement (j : Lean.Json) : CoreM Statement :=
  (parseJsonReturn j) <|> (parseJsonInvocation j)

def parseJsonDeclaration (j : Lean.Json) :
    CoreM (Identifier × Nat × List (Nat × Identifier) × List Identifier) := do
  let .ok id := j.getObjVal? "id"
    | throwError "declaration must include id"
  let .ok (.str id) := id.getObjVal? "debug_name"
    | throwError "dbug_name must be a string!"
  let .ok id ← parseIdentifier id
    | throwError "cannot parse lhs identifier of type def"
  let .ok (.num ⟨.ofNat n, 0⟩) := j.getObjVal? "entry_point"
    | throwError "declaration must include entry_point"
  let .ok signature := j.getObjVal? "signature"
    | throwError "declaration must include signature"
  let .ok (.arr param_types) := signature.getObjVal? "param_types"
    | throwError "signature must contain array of param_types"
  let .ok param_types := param_types.mapM ((·.getObjVal? "debug_name"))
    | throwError "param_types must contain debug_name"
  let .ok param_types := param_types.mapM Json.getStr?
    | throwError "debug_name of all param_types must be a string"
  let param_types ← param_types.mapM parseIdentifier
  let .ok param_types := param_types.mapM (·)
    | throwError "cannot parse param_type as identifier"
  let .ok (.arr ret_types) := signature.getObjVal? "ret_types"
    | throwError "signature must contain array of ret_types"
  let .ok ret_types := ret_types.mapM ((·.getObjVal? "debug_name"))
    | throwError "ret_types must contain debug_name"
  let .ok ret_types := ret_types.mapM Json.getStr?
    | throwError "debug_name of all ret_types must be a string"
  let ret_types ← ret_types.mapM parseIdentifier
  let .ok ret_types := ret_types.mapM (·)
    | throwError "cannot parse ret_types as identifier"
  let .ok (.arr params) := j.getObjVal? "params"
    | throwError "signature must contain array of params"
  let .ok params := params.mapM ((·.getObjVal? "id"))
    | throwError "params must contain id"
  let .ok params := params.mapM ((·.getObjVal? "id"))
    | throwError "params' id must contain id"
  let .ok params := params.mapM Json.getNum?
    | throwError "id of all params must be a number"
  let params ← params.mapM fun s =>
    match s with
    | ⟨.ofNat n,0⟩ => pure n
    | _ => throwError "id of all params must be positive integer"
  pure (id, n, (params.zip param_types).toList, ret_types.toList)

def parseJson (j : Lean.Json) : CoreM SierraFile := do
  -- Descend into "sierra_program" if we are in the output of snforge
  let j := match j.getObjVal? "sierra_program" with
    | .ok j' => j'
    | .error _ => j
  let .ok (.arr typedefs) := j.getObjVal? "type_declarations"
    | throwError "Typedefs must be an array!"
  let typedefs ← typedefs.mapM parseJsonDef
  let .ok (.arr libfuncs) := j.getObjVal? "libfunc_declarations"
    | throwError "Libfuncs must be an array!"
  let libfuncs ← libfuncs.mapM parseJsonDef
  let .ok (.arr statements) := j.getObjVal? "statements"
    | throwError "Statements must be an array!"
  let statements ← statements.mapM parseJsonStatement
  let .ok (.arr declarations) := j.getObjVal? "funcs"
    | throwError "Declaractions must be an array!"
  let declarations ← declarations.mapM parseJsonDeclaration
  pure { typedefs := typedefs.toList
         libfuncs := libfuncs.toList
         statements := statements.toList
         declarations := declarations.toList }
