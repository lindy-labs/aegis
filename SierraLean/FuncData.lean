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

instance : ToString RefTable where toString x := toString $ repr x.toList

/-- A structure containing all necessary data to process a libfunc -/
structure FuncData (i : Identifier) where
  /-- The types of the arguments, empty by default -/
  (inputTypes : List Type := [])
  /-- The number of branches, `1` by default -/
  (Branches : Type := Unit)
  /-- The return types of each branch -/
  (outputTypes : Branches → List Type := fun _ => [])
  /-- The condition for each branch -/
  (condition : (b : Branches) → OfInputs Prop (inputTypes ++ outputTypes b) :=
    fun _ => OfInputs.const <| True)
  (refsChange : RefTable → List ℕ → RefTable := fun rt _ => rt)

instance : Inhabited (FuncData i) := ⟨{ outputTypes := fun _ => default,
                                        condition := fun _ => OfInputs.const True }⟩

def FuncData.felt252_const (n : Nat) : FuncData (.name "felt252_const" [.const n]) where
  inputTypes := []
  outputTypes := fun _ => [F]
  condition := fun _ a => a = (n : F)

def FuncData.felt252_add : FuncData (.name "felt252_add" []) where
  condition := fun _ a b ρ => ρ = a + b
  inputTypes := [F, F]
  outputTypes := fun _ => [F]

def FuncData.felt252_sub : FuncData (.name "felt252_sub" []) where
  condition := fun _ a b ρ => ρ = a - b
  inputTypes := [F, F]
  outputTypes := fun _ => [F]

def FuncData.felt252_mul : FuncData (.name "felt252_mul" []) where
  inputTypes := [F, F]
  outputTypes := fun _ => [F]
  condition := fun _ a b ρ => ρ = a * b

def FuncData.rename (T) : FuncData (.name "rename" [T]) where
  inputTypes := [Addr]
  outputTypes := fun _ => [Addr]
  refsChange rt args := match args with
    | [a, ρ] => (rt.insert ρ (rt.find! a)).erase a
    | _ => panic "Wrong number of arguments supplied to rename()"
  condition := fun _ _ _ => True

def FuncData.drop (T) : FuncData (.name "drop" [T]) where
  inputTypes := [Addr]
  outputTypes := fun _ => []
  refsChange rt args := match args with
    | [a] => rt.erase a
    | _ => panic "Wrong number of arguments supplied to drop()"
  condition := fun _ _ => True

def FuncData.dup (T) : FuncData (.name "dup" [T]) where
  inputTypes := [Addr]
  outputTypes := fun _ => [Addr, Addr]
  refsChange rt args := match args with
    | [a, ρ₁, ρ₂] => let fv := rt.find! a
                     ((rt.insert ρ₁ fv).insert ρ₂ fv).erase a
    | _ => panic "Wrong number of arguments supplied to dup()"
  condition := fun _ _ _ _ => True

def FuncData.store_temp (T) : FuncData (.name "store_temp" [T]) where
  inputTypes := [Addr]
  outputTypes := fun _ => [Addr]
  refsChange rt args := match args with
    | [a, ρ] => rt.insert ρ (rt.find! a)
    | _ => panic "Wrong number of arguments supplied to store_temp()"
  condition := fun _ _ _ => True

-- Does nothing internally to Sierra
def FuncData.branch_align : FuncData (.name "branch_align" []) where
  inputTypes := []
  outputTypes := fun _ => []
  condition := fun _ => True

def FuncData.jump : FuncData (.name "jump" []) where
  inputTypes := []
  outputTypes := fun _ => []
  condition := fun _ => True
  
/-- Compile-time function data register -/
def FuncData_register : (i : Identifier) → FuncData i
| .name "felt252_const" [.const n] => FuncData.felt252_const n
| .name "felt252_add" []           => FuncData.felt252_add
| .name "felt252_sub" []           => FuncData.felt252_sub
| .name "felt252_mul" []           => FuncData.felt252_mul
| .name "rename" [T]               => FuncData.rename T
| .name "drop" [T]                 => FuncData.drop T
| .name "store_temp" [T]           => FuncData.store_temp T
| .name "dup" [T]                  => FuncData.dup T
| .name "branch_align" []          => FuncData.branch_align
| .name "jump" []                  => FuncData.jump
| _ => panic "FuncData not found in register"

/-- Compile-time type registry -/
def Type_register : (i : Identifier) → Expr
| .name "felt252" [] => mkConst ``Sierra.F
| _ => panic "Type not found in register"
