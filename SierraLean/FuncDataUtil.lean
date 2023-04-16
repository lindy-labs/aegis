import SierraLean.Parser
import SierraLean.ExprUtil

open Lean Qq

namespace Sierra

abbrev RefTable := HashMap Nat FVarId

instance : ToString RefTable where toString x := toString $ repr x.toList

/-- A structure contining the branch-specific data for a libfunc -/
structure BranchData (inputTypes : List Q(Type)) where
  /-- The return types -/
  (outputTypes : List Q(Type) := [])
  /-- The condition associated with the branch -/
  (condition : OfInputs Q(Prop) (inputTypes ++ outputTypes) := OfInputs.const <| q(True))
  /-- Ref table changes, only used for memory management commands -/
  (refsChange : List Nat → RefTable → RefTable := fun _ rt => rt)

instance : Inhabited (BranchData inputTypes) := ⟨{ }⟩

/-- A structure containing all necessary data to process a libfunc -/
structure FuncData where
  /-- The types of the arguments, empty by default -/
  (inputTypes : List Q(Type) := [])
  /-- The list of branches, one branch by default -/
  (branches : List (BranchData inputTypes) := [{ }])

instance : Inhabited FuncData := ⟨{ }⟩
