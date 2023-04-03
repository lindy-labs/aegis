import SierraLean.Parser
import Mathlib.Data.ZMod.Basic
import Qq

open Lean Qq

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
  (refTypes : HashMap Nat Q(Type 1))
  (conditions : List Expr)

structure FuncData (i : Identifier) where
  (inputTypes : List Type := [])
  (outputTypes : List Type := [])
  (condition : OfInputs Prop (inputTypes ++ outputTypes) := OfInputs.const True)
  (refsChange : OfInputs (RefTable → RefTable) (inputTypes ++ outputTypes) := OfInputs.const id)
  (pcChange : Nat → Nat := (· + 1))

instance : Inhabited (FuncData i) := ⟨{  }⟩

def FuncData.felt252_const (n : Nat) : FuncData (.name "felt252_const" [.const n]) where
  inputTypes := []
  outputTypes := [F]
  condition := fun a => a = (n : F)

def FuncData.felt252_add : FuncData (.name "felt252_add" []) where
  condition := fun a b ρ => ρ = a + b
  inputTypes := [F, F]
  outputTypes := [F]

def FuncData.felt252_sub : FuncData (.name "felt252_sub" []) where
  condition := fun a b ρ => ρ = a - b
  inputTypes := [F, F]
  outputTypes := [F]

def FuncData.felt252_mul : FuncData (.name "felt252_mul" []) where
  inputTypes := [F, F]
  outputTypes := [F]
  condition := fun a b ρ => ρ = a * b

def FuncData.rename : FuncData (.name "rename" [T]) where
  inputTypes := [Addr]
  outputTypes := [Addr]
  refsChange := fun a ρ rt => (rt.insert ρ (rt.find! a)).erase a  -- TODO think about whether this is really it

def FuncData.dup : FuncData (.name "dup" []) where
  inputTypes := [Addr]
  outputTypes := [Addr, Addr]
  refsChange := fun a ρ₁ ρ₂ rt => 
    let fv := rt.find! a
    ((rt.insert ρ₁ fv).insert ρ₂ fv).erase a

def FuncData.storeTemp : FuncData (.name "storeTemp" []) where
  inputTypes := [Addr]
  outputTypes := [Addr]
  refsChange := fun a ρ rt => rt.insert ρ (rt.find! a)

def FuncData_register : (i : Identifier) → FuncData i
| .name "felt252_const" [.const n] => FuncData.felt252_const n
| .name "felt252_add" [] => FuncData.felt252_add
| .name "felt252_sub" [] => FuncData.felt252_sub
| .name "felt252_mul" [] => FuncData.felt252_mul
| _ => panic "FuncData not found in register"
