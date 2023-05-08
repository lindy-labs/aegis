import SierraLean.FuncDataUtil

open Qq Lean Sierra

namespace Sierra.FuncData

def box_into (t : SierraType) : FuncData where
  inputTypes := [t]
  branches := [{ outputTypes := [.Box t], condition := fun (a ρ : Expr) => q($ρ = $a) }]

def unbox (t : SierraType) : FuncData where
  inputTypes := [.Box t]
  branches := [{ outputTypes := [t], condition := fun (a ρ : Expr) => q($ρ = $a) }]

def boxLibfuncs (typeRefs : HashMap Identifier SierraType) : Identifier → Option FuncData
| .name "box_into" [.identifier ident] _ =>
  match typeRefs.find? ident with
  | .some t => box_into t
  | _ => .none
| .name "unbox" [.identifier ident] _ =>
  match typeRefs.find? ident with
  | .some t => unbox t
  | _ => .none
| _ => .none
