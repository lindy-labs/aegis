import SierraLean.Parser
import SierraLean.ExprUtil
import Mathlib.Data.ZMod.Basic

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

def PRIME := 3618502788666131213697322783095070105623107215331596699973092056135872020481

abbrev F := ZMod PRIME

abbrev UInt128 := ZMod <| 2^128

def enum (fields : List Q(Type)) : Q(Type) :=
  let f := listToExpr fields
  q(Σ (i : Fin ($f).length), ($f).get i)

mutual

inductive ResolvedParameter where
| const (n : Int)
| identifier (i : ResolvedIdentifier)
deriving Inhabited, Repr

inductive ResolvedIdentifier where
| name (str : String) (ps : List ResolvedParameter)
deriving Inhabited, Repr

end

instance : ToString ResolvedParameter where toString x := toString $ repr x
instance : ToString ResolvedIdentifier where toString x := toString $ repr x

partial def resolveParameter (typeRefs : HashMap Identifier ResolvedIdentifier) :
    Parameter → ResolvedParameter
| .identifier i
| .userfunc i
| .libfunc i
| .usertype i =>
  match typeRefs.find? i with
  | .some i' => .identifier i'
  | .none =>
    match i with
    | .name str ps => .identifier <| .name str <| resolveParameter typeRefs <$> ps
    | _ => panic "cannot resolve parameters"
| .const n => .const n

def toResolvedIdentifiers : List ResolvedParameter → List ResolvedIdentifier :=
List.filterMap <| fun p => match p with
  | .identifier i => i
  | _ => .none

mutual

/-- Compile-time type registry -/ -- TODO decentralize this
partial def Type_register (typeRefs : HashMap Identifier ResolvedIdentifier) :
    ResolvedIdentifier → Q(Type)
| .name "felt252" [] => q(F)
| .name "u128" []    => q(UInt128)
| .name "Enum" (_ :: fields) => Enum typeRefs (toResolvedIdentifiers fields)
| i@_ => panic <| "Type not found in register: " ++ toString (repr i)

partial def Enum (typeRefs : HashMap Identifier ResolvedIdentifier)
    (fields : List ResolvedIdentifier) : Q(Type) :=
  enum <| fields.map fun ident => Type_register typeRefs ident

end
