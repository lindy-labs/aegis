import Aegis.Parser

open Lean Sierra PrettyPrinter Delaborator SubExpr

elab:max "id!" s:str : term => do
  let s := replaceNaughtyBrackets s.getString
  match ← parseIdentifier s with
  | .ok i => pure <| ToExpr.toExpr i
  | .error e => throwError "Unable to elaborate identifier String:\n{e}"

@[app_unexpander Sierra.Identifier.ref]
def unexpandIdentifierRef : Unexpander
| `($_ $n:num) => do
  let s := ToString.toString (Identifier.ref n.getNat)
  `(id!$(quote s))
| _ => throw ()

@[app_unexpander Sierra.Identifier.name]
def unexpandIdentifierName : Unexpander
| `($_ $i:str $ps $tl) => do
  let ps ← match ps with
  | `([]) => pure ""
  | `([$ps,*]) =>
    let ps := ps.getElems
    let ps : Array String ← ps.mapM fun p =>
      match p with
      | `(Parameter.identifier $x) =>
        match x with | `(id!$s) => pure s.getString | _ => throw ()
      | `(Parameter.usertype $x) =>
        match x with | `(id!$s) => pure <| "ut@" ++ s.getString | _ => throw ()
      | `(Parameter.userfunc $x) =>
        match x with | `(id!$s) => pure <| "user@" ++ s.getString | _ => throw ()
      | `(Parameter.libfunc $x) =>
        match x with | `(id!$s) => pure <| "lib@" ++ s.getString | _ => throw ()
      | `(Parameter.const $x) =>
        match x with | `(Int.ofNat $n:num) => pure n.getNat.repr | _ => throw ()
      | _ => throw ()
    pure <| "<" ++ String.intercalate "," ps.toList ++ ">"
  | _ => throw ()
  let tl ← match tl with
  | `(none) => pure ""
  | `(some $x) => match x with | `(id!$s) => pure <| "::" ++ s.getString | _ => throw ()
  | _ => throw ()
  `(id!$(quote <| i.getString ++ ps ++ tl))
| _ => throw ()
