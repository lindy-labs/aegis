import SierraLean.Parser
import SierraLean.ExprUtil
import Mathlib.Data.ZMod.Basic

open Lean Qq

namespace Sierra

abbrev Addr := Nat

def PRIME := 3618502788666131213697322783095070105623107215331596699973092056135872020481

abbrev F := ZMod PRIME

-- TODO this has to exist somewhere?


abbrev RefTable := HashMap Nat FVarId

instance : ToString RefTable where toString x := toString $ repr x.toList

/-- A structure contining the branch-specific data for a libfunc -/
structure BranchData (inputTypes : List Q(Type)) where
  /-- The return types -/
  (outputTypes : List Q(Type) := [])
  /-- The condition associated with the branch -/
  (condition : OfInputs Q(Prop) (inputTypes ++ outputTypes) := OfInputs.const <| q(True))
  /-- Ref table changes, only used for memory management commands -/
  (refsChange : List ℕ → RefTable → RefTable := fun _ rt => rt)

instance : Inhabited (BranchData inputTypes) := ⟨{ }⟩

/-- A structure containing all necessary data to process a libfunc -/
structure FuncData where
  /-- The types of the arguments, empty by default -/
  (inputTypes : List Q(Type) := [])
  /-- The list of branches, one branch by default -/
  (branches : List (BranchData inputTypes) := [{ }])

instance : Inhabited FuncData := ⟨{ }⟩

def FuncData.felt252_const (n : Q(Nat)) : FuncData where
  inputTypes := []
  branches := [{ outputTypes := [q(F)], condition := fun a => q($a = ($n : F)) }]

def FuncData.felt252_add : FuncData where
  inputTypes := [q(F), q(F)]
  branches := [{ outputTypes := [q(F)], condition := fun a b ρ => q($ρ = $a + $b) }]

def FuncData.felt252_sub : FuncData where
  inputTypes := [q(F), q(F)]
  branches := [{ outputTypes := [q(F)], condition := fun a b ρ => q($ρ = $a - $b) }]

def FuncData.felt252_mul : FuncData where
  inputTypes := [q(F), q(F)]
  branches := [{ outputTypes := [q(F)], condition := fun a b ρ => q($ρ = $a * $b) }]

def FuncData.felt252_is_zero : FuncData where
  inputTypes := [q(F)]
  branches := [{ outputTypes := [],
                 condition := fun a => q($a = 0) },
               { outputTypes := [q(F)], -- TODO Actually the condition is baked into the output type here
                 condition := fun a _ => q($a ≠ 0) }]

def FuncData.rename : FuncData where
  inputTypes := [q(Addr)]
  branches := [{ outputTypes := [q(Addr)],
                 refsChange := fun aρ rt => match aρ with
                  | [a, ρ] => (rt.insert ρ (rt.find! a)).erase a
                  | _ => panic! "Wrong number of arguments supplied to rename()" }]

def FuncData.drop : FuncData where
  inputTypes := [q(Addr)]
  branches := [{ outputTypes := [],
                 refsChange := fun a rt => match a with
                  | [a] => rt.erase a
                  | _ => panic! "Wrong number of arguments supplied to drop()" }]

def FuncData.dup : FuncData where
  inputTypes := [q(Addr)]
  branches := [{ outputTypes := [q(Addr), q(Addr)],
                 refsChange := fun aρ₁ρ₂ rt => match aρ₁ρ₂ with
                  | [a, ρ₁, ρ₂] => let fv := rt.find! a
                    ((rt.insert ρ₁ fv).insert ρ₂ fv).erase a
                  | _ => panic! "Wrong number of arguments supplied to dup()" }]

def FuncData.store_temp : FuncData where
  inputTypes := [q(Addr)]
  branches := [{ outputTypes := [q(Addr)],
                 refsChange := fun aρ rt => match aρ with
                  | [a, ρ] => rt.insert ρ (rt.find! a)
                  | _ => panic! "Wrong number of arguments supplied to store_temp()" }]

-- Does nothing internally to Sierra
def FuncData.branch_align : FuncData where

def FuncData.jump : FuncData where

/-- Compile-time function data register -/
def FuncData_register : Identifier → FuncData
| .name "felt252_const" [.const n] => FuncData.felt252_const q($n)
| .name "felt252_add" []           => FuncData.felt252_add
| .name "felt252_sub" []           => FuncData.felt252_sub
| .name "felt252_mul" []           => FuncData.felt252_mul
| .name "felt252_is_zero" []       => FuncData.felt252_is_zero
| .name "rename" [_]               => FuncData.rename
| .name "drop" [_]                 => FuncData.drop
| .name "store_temp" [_]           => FuncData.store_temp
| .name "dup" [_]                  => FuncData.dup
| .name "branch_align" []          => FuncData.branch_align
| .name "jump" []                  => FuncData.jump
| _ => panic "FuncData not found in register"

/-- Compile-time type registry -/
def Type_register : (i : Identifier) → Expr
| .name "felt252" [] => mkConst ``Sierra.F
| _ => panic "Type not found in register"
