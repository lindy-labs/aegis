import SierraLean.Parser

open Lean Sierra PrettyPrinter

syntax "`[id|" identifier "]" : term
syntax "`[param|" parameter "]" : term

macro_rules
| `(`[id|$[@]? $i:ident $[[$j:ident]]? $[$[::]? <$ps,*>]? $[:: $tl:identifier]?]) => do
  let tl ← tl.elim `(term|.none) fun tl => `(term|`[id|$tl])
  let ps ← ps.elim `(term|[]) fun ps => do
    let ps ← ps.getElems.mapM fun p => `(term|`[param|$p])
    `(term|$(quote ps.toList))
  `(term|Identifier.name $(quote i.getId.toString) $ps $tl)
| `(`[id|return]) => `(Identifier.name "return" [] .none)
| `(`[id|[$num]]) => `(Identifier.ref $num)
| `(`[param|$i:identifier]) => `(.identifier `[id|$i])
| `(`[param|ut@$i:identifier]) => `(.usertype `[id|$i])
| `(`[param|user@$i:identifier]) => `(.userfunc `[id|$i])
| `(`[param|lib@$i:identifier]) => `(.libfunc `[id|$i])
| `(`[param|$n:num]) => `(.const $n)
| `(`[param|-$n:num]) => `(.const (-$n))

@[app_unexpander Sierra.Identifier.ref]
def unexpandIdentifierRef : Unexpander
| `($_ $n:num) => `(`[id|[$n]])
| _ => throw ()

@[app_unexpander Sierra.Identifier.name]
def unexpandIdentifierName : Unexpander
| `($_ $i:str $ps none) => `(`[id|$(mkIdent i.getString):ident])
| _ => throw ()
