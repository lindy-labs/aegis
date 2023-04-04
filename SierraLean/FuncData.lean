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

/-- A structure containing all necessary data to process a libfunc -/
structure FuncData (i : Identifier) where
  (inputTypes : List Type := [])
  (outputTypes : List Type := [])
  (condition : OfInputs Prop (inputTypes ++ outputTypes) := OfInputs.const True)
  (refsChange : RefTable → List ℕ → RefTable := fun rt _ => rt)
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

def FuncData.rename (T) : FuncData (.name "rename" [T]) where
  inputTypes := [Addr]
  outputTypes := [Addr]
  refsChange rt args := match args with
    | [a, ρ] => (rt.insert ρ (rt.find! a)).erase a
    | _ => panic "Wrong number of arguments supplied to rename()"

def FuncData.drop (T) : FuncData (.name "drop" [T]) where
  inputTypes := [Addr]
  outputTypes := []
  refsChange rt args := match args with
    | [a] => rt.erase a
    | _ => panic "Wrong number of arguments supplied to drop()"

def FuncData.dup : FuncData (.name "dup" []) where
  inputTypes := [Addr]
  outputTypes := [Addr, Addr]
  refsChange rt args := match args with
    | [a, ρ₁, ρ₂] => let fv := rt.find! a
                     ((rt.insert ρ₁ fv).insert ρ₂ fv).erase a
    | _ => panic "Wrong number of arguments supplied to dup()"

def FuncData.store_temp (T) : FuncData (.name "store_temp" [T]) where
  inputTypes := [Addr]
  outputTypes := [Addr]
  refsChange rt args := match args with
    | [a, ρ] => rt.insert ρ (rt.find! a)
    | _ => panic "Wrong number of arguments supplied to store_temp()"

/-- Compile-time function data register -/
def FuncData_register : (i : Identifier) → FuncData i
| .name "felt252_const" [.const n] => FuncData.felt252_const n
| .name "felt252_add" []           => FuncData.felt252_add
| .name "felt252_sub" []           => FuncData.felt252_sub
| .name "felt252_mul" []           => FuncData.felt252_mul
| .name "rename" [T]               => FuncData.rename T
| .name "drop" [T]                 => FuncData.drop T
| .name "store_temp" [T]           => FuncData.store_temp T
| _ => panic "FuncData not found in register"

/-- Compile-time type registry -/
def Type_register : (i : Identifier) → Expr
| .name "felt252" [] => mkConst ``Sierra.F
| _ => panic "Type not found in register"
