import SierraLean.FuncDataUtil

open Qq Lean Sierra

namespace Sierra.FuncData

def rename (t : SierraType) : FuncData where
  inputTypes := [t]
  branches := [{ outputTypes := [t]
                 condition := fun (a ρ : Expr) => Expr.mkEq q($(⟦t⟧)) ρ a
                 /- refsChange := fun aρ rt => match aρ with
                  | [a, ρ] => (rt.insert ρ (rt.find! a)).erase a
                  | _ => panic! "Wrong number of arguments supplied to rename()" -/ } ]

def drop (t : SierraType) : FuncData where
  inputTypes := [t]
  branches := [{ outputTypes := []
                 refsChange := fun a rt => match a with
                  | [a] => rt.erase a
                  | _ => panic! "Wrong number of arguments supplied to drop()" }]

def dup (t : SierraType) : FuncData where
  inputTypes := [t]
  branches := [{ outputTypes := [t, t]
                 condition := fun (a ρ₁ ρ₂ : Expr) =>
                   Expr.mkAnds [Expr.mkEq q($(⟦t⟧)) ρ₁ a, Expr.mkEq q($(⟦t⟧)) ρ₂ a]
                   --q($(Expr.mkEq qt ρ₁ a) ∧ $ρ₂ = $a)
                 /-refsChange := fun aρ₁ρ₂ rt => match aρ₁ρ₂ with
                  | [a, ρ₁, ρ₂] => let fv := rt.find! a
                    ((rt.insert ρ₁ fv).insert ρ₂ fv).erase a
                  | _ => panic! "Wrong number of arguments supplied to dup()"-/ }]

def store_temp (t : SierraType) : FuncData where
  inputTypes := [t]
  branches := [{ outputTypes := [t],
                 condition := fun (a ρ : Expr) => Expr.mkEq q($(⟦t⟧)) ρ a
                 /- refsChange := fun aρ rt => match aρ with
                  | [a, ρ] => rt.insert ρ (rt.find! a)
                  | _ => panic! "Wrong number of arguments supplied to store_temp()" -/ }]

-- Does nothing internally to Sierra
def branch_align : FuncData where

def jump : FuncData where

def controlFlowLibfuncs (typeRefs : HashMap Identifier SierraType) : Identifier → Option FuncData
| .name "rename" [.identifier ident] => return rename (← typeRefs.find? ident)
| .name "drop" [.identifier ident] => return drop (← typeRefs.find? ident)
| .name "store_temp" [.identifier ident] => return store_temp (← typeRefs.find? ident)
| .name "dup" [.identifier ident] => return dup (← typeRefs.find? ident)
| .name "branch_align" [] => FuncData.branch_align
| .name "jump" [] => FuncData.jump
| _  => .none
