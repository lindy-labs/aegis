import SierraLean.Parser
import SierraLean.ExprUtil
import Mathlib.Data.ZMod.Basic

open Lean Qq

namespace Sierra

def Addr := Nat

inductive SierraType
| Felt252
| U32
| U64
| U128
| U256
| SierraBool
| Addr
| RangeCheck
| Enum (fields : List SierraType)
| Struct (fields : List SierraType)
| NonZero (ty : SierraType)
| Box (ty : SierraType)
| Snapshot (ty : SierraType)
| Array (ty : SierraType)
  deriving Inhabited, Repr

abbrev RefTable := HashMap Nat FVarId

instance : ToString RefTable where toString x := toString $ repr x.toList

def PRIME := 3618502788666131213697322783095070105623107215331596699973092056135872020481

abbrev F := ZMod PRIME

abbrev UInt32 := ZMod <| 2^32
abbrev UInt64 := ZMod <| 2^64
abbrev UInt128 := ZMod <| 2^128
abbrev UInt256 := ZMod <| 2^256

def enum (fields : List Q(Type)) : Q(Type) :=
  let f := listToExpr fields
  q(Σ (i : Fin ($f).length), ($f).get i)

def struct (fields : List Q(Type)) : Q(Type) :=
  let f := listToExpr fields
  q(∀ (i : Fin ($f).length), ($f).get i)

partial def SierraType.toQuote : SierraType → Q(Type)
  | .Felt252 => q(F)
  | .U32 => q(UInt32)
  | .U64 => q(UInt64)
  | .U128 => q(UInt128)
  | .U256 => q(UInt256)
  | .SierraBool => q(Bool)
  | .Addr => q(Sierra.Addr)
  | .RangeCheck => q(Nat)  -- TODO
  | .Enum fields => enum <| fields.map toQuote
  | .Struct fields => struct <| fields.map toQuote
  | .NonZero t => toQuote t -- TODO Maybe change to `{x : F // x ≠ 0}` somehow
  | .Box t => toQuote t
  | .Snapshot t => toQuote t
  | .Array t => q(List $(toQuote t))

/-- A structure contining the branch-specific data for a libfunc -/
structure BranchData (inputTypes : List SierraType) where
  /-- The return types -/
  (outputTypes : List SierraType := [])
  /-- The condition associated with the branch -/
  (condition : OfInputs Q(Prop) (List.map SierraType.toQuote <| inputTypes ++ outputTypes) := OfInputs.const <| q(True))
  /-- Ref table changes, only used for memory management commands -/
  (refsChange : List Nat → RefTable → RefTable := fun _ rt => rt)

instance : Inhabited (BranchData inputTypes) := ⟨{ }⟩

/-- A structure containing all necessary data to process a libfunc -/
structure FuncData where
  /-- The types of the arguments, empty by default -/
  (inputTypes : List SierraType := [])
  /-- The list of branches, one branch by default -/
  (branches : List (BranchData inputTypes) := [{ }])

instance : Inhabited FuncData := ⟨{ }⟩
