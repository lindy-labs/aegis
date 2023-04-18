import SierraLean.FuncDataUtil
import SierraLean.FuncData.Felt252

open Qq Lean Meta Sierra

namespace Sierra.FuncData

def enum_init (fields : List Q(Type)) (idx : Fin fields.length) : FuncData where
  inputTypes := [fields.get idx]
  branches := [{ outputTypes := [enum fields],
                 condition := fun a ρ =>
                   Expr.mkAnds [Expr.mkEq q(Fin $(listToExpr fields).length) q($ρ.1.val) (toExpr idx.val),
                     Expr.mkEq q($(fields.get idx)) q($ρ.2) q($a)] }]

def enumLibfuncs (typeRefs : HashMap Identifier ResolvedIdentifier) : Identifier → Option FuncData
| .name "enum_init" [.identifier ident, .const (.ofNat n)] =>
  match typeRefs.find? ident with
  | .some (.name "Enum" (_::fields)) =>
    dbg_trace "before dereferencing: {fields}"
    let fields := toResolvedIdentifiers fields
    let fields := fields.map (Type_register typeRefs)
    dbg_trace "after resolving types: {fields}"
    if hn : n < fields.length then enum_init fields ⟨n, hn⟩
    else .none
  | _ => .none
| _ => .none
