import SierraLean.FuncDataUtil
import SierraLean.FuncData.Felt252

open Qq Lean Meta Sierra

namespace Sierra.FuncData

def enum_init (fields : List SierraType) (idx : Fin fields.length) : FuncData where
  inputTypes := [SierraType.toQuote <| fields.get idx]
  branches := [{ outputTypes := [enum <| fields.map SierraType.toQuote],
                 condition := fun a ρ =>
                   Expr.mkAnds [
                    Expr.mkEq
                      q(Fin $(listToExpr <| fields.map SierraType.toQuote).length)
                      q($ρ.1.val)
                      (toExpr idx.val),
                    Expr.mkEq q($(SierraType.toQuote <| fields.get idx)) q($ρ.2) q($a)] }]

def enumLibfuncs (typeRefs : HashMap Identifier SierraType) : Identifier → Option FuncData
| .name "enum_init" [.identifier ident, .const (.ofNat n)] =>
  match typeRefs.find? ident with
  | .some (.Enum _ fields) =>
    if hn : n < fields.length then enum_init fields ⟨n, hn⟩
    else .none
  | _ => .none
| _ => .none
