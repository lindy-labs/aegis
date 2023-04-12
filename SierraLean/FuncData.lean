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

/-- A structure contining the branch-specific data for a libfunc -/
structure BranchData (inputTypes : List Type) where
  /-- The return types -/
  (outputTypes : List Type := [])
  /-- The condition associated with the branch -/
  (condition : OfInputs Prop (inputTypes ++ outputTypes) := OfInputs.const <| True)
  /-- Ref table changes, only used for memory management commands -/
  (refsChange : List ℕ → RefTable → RefTable := fun _ rt => rt)

instance : Inhabited (BranchData inputTypes) := ⟨{  }⟩

/-- A structure containing all necessary data to process a libfunc -/
structure FuncData (i : Identifier) where
  /-- The types of the arguments, empty by default -/
  (inputTypes : List Type := [])
  /-- The list of branches, one branch by default -/
  (branches : List (BranchData inputTypes) := [{ }])

instance : Inhabited (FuncData i) := ⟨{ }⟩

def FuncData.felt252_const (n : Nat) : FuncData (.name "felt252_const" [.const n]) where
  inputTypes := []
  branches := [{ outputTypes := [F], condition := fun a => a = (n : F) }]

def FuncData.felt252_add : FuncData (.name "felt252_add" []) where
  inputTypes := [F, F]
  branches := [{ outputTypes := [F], condition := fun a b ρ => ρ = a + b }]

def FuncData.felt252_sub : FuncData (.name "felt252_sub" []) where
  inputTypes := [F, F]
  branches := [{ outputTypes := [F], condition := fun a b ρ => ρ = a - b }]

def FuncData.felt252_mul : FuncData (.name "felt252_mul" []) where
  inputTypes := [F, F]
  branches := [{ outputTypes := [F], condition := fun a b ρ => ρ = a * b }]

def FuncData.felt252_is_zero : FuncData (.name "felt252_zero" []) where
  inputTypes := [F]
  branches := [{ outputTypes := [],
                 condition := fun a => a = 0 },
               { outputTypes := [F], -- TODO Actually the condition is baked into the output type here
                 condition := fun a _ => a ≠ 0 }]

def FuncData.rename (T) : FuncData (.name "rename" [T]) where
  inputTypes := [Addr]
  branches := [{ outputTypes := [Addr],
                 refsChange := fun aρ rt => match aρ with
                  | [a, ρ] => (rt.insert ρ (rt.find! a)).erase a
                  | _ => panic! "Wrong number of arguments supplied to rename()" }]

def FuncData.drop (T) : FuncData (.name "drop" [T]) where
  inputTypes := [Addr]
  branches := [{ outputTypes := [],
                 refsChange := fun a rt => match a with
                  | [a] => rt.erase a
                  | _ => panic! "Wrong number of arguments supplied to drop()" }]

def FuncData.dup (T) : FuncData (.name "dup" [T]) where
  inputTypes := [Addr]
  branches := [{ outputTypes := [Addr, Addr],
                 refsChange := fun aρ₁ρ₂ rt => match aρ₁ρ₂ with
                  | [a, ρ₁, ρ₂] => let fv := rt.find! a
                    ((rt.insert ρ₁ fv).insert ρ₂ fv).erase a
                  | _ => panic! "Wrong number of arguments supplied to dup()" }]

def FuncData.store_temp (T) : FuncData (.name "store_temp" [T]) where
  inputTypes := [Addr]
  branches := [{ outputTypes := [Addr],
                 refsChange := fun aρ rt => match aρ with
                  | [a, ρ] => rt.insert ρ (rt.find! a)
                  | _ => panic! "Wrong number of arguments supplied to store_temp()" }]

-- Does nothing internally to Sierra
def FuncData.branch_align : FuncData (.name "branch_align" []) where

def FuncData.jump : FuncData (.name "jump" []) where
  
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
