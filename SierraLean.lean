import SierraLean.Parser
import Mathlib.Data.ZMod.Basic

open Lean

namespace Sierra

abbrev Addr := Nat

def PRIME := 3618502788666131213697322783095070105623107215331596699973092056135872020481

abbrev F := ZMod PRIME

-- TODO this has to exist somewhere?
def OfInputs (R : Type) : List Type → Type
| []        => R
| (T :: Ts) => T → OfInputs R Ts

def OfInputs.const {R : Type} (r : R) : {Ts : List Type} → OfInputs R Ts
| []       => r
| (_ :: _) => fun _ => OfInputs.const r

abbrev RefTable := HashMap Nat FVarId

structure state
  (refFVars : HashMap Nat FVarId)
  (refTypes : HashMap Nat Expr)
  (conditions : List Expr)

class FuncData (i : Identifier) where
  (inputTypes : List Type := [])
  (outputTypes : List Type := [])
  (condition : OfInputs Prop (inputTypes ++ outputTypes) := OfInputs.const True)
  (refsChange : OfInputs (RefTable → RefTable) (inputTypes ++ outputTypes) := OfInputs.const id)
  (pcChange : OfInputs (Nat → Nat) (inputTypes ++ outputTypes) := OfInputs.const (· + 1))
  
instance : FuncData (.name "felt252_const" [.const n]) where
  inputTypes := []
  outputTypes := [F]
  condition := fun a => a = (n : F)

instance : FuncData (.name "felt252_add" []) where
  condition := fun a b ρ => ρ = a + b
  inputTypes := [F, F]
  outputTypes := [F]

instance : FuncData (.name "felt252_sub" []) where
  condition := fun a b ρ => ρ = a - b
  inputTypes := [F, F]
  outputTypes := [F]

instance : FuncData (.name "rename" [T]) where
  inputTypes := [Addr]
  outputTypes := [Addr]
  refsChange := fun a ρ rt => (rt.insert ρ (rt.find! a)).erase a  -- TODO think about whether this is really it

instance : FuncData (.name "dup" []) where
  inputTypes := [Addr]
  outputTypes := [Addr, Addr]
  refsChange := fun a ρ₁ ρ₂ rt => 
    let fv := rt.find! a
    ((rt.insert ρ₁ fv).insert ρ₂ fv).erase a

instance : FuncData (.name "storeTemp" []) where
  inputTypes := [Addr]
  outputTypes := [Addr]
  refsChange := fun a ρ rt => rt.insert ρ (rt.find! a)
