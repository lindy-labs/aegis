import SierraLean.Parser
import SierraLean.ExprUtil
import Mathlib.Data.ZMod.Basic

open Lean Qq

namespace Sierra

def Addr := Nat

inductive SierraType
| Felt252
| U8
| U16
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
| U128MulGuarantee
| Pedersen
| BuiltinCosts
| GasBuiltin
  deriving Inhabited, Repr

abbrev RefTable := HashMap Nat FVarId

instance : ToString RefTable where toString x := toString $ repr x.toList

def PRIME := 3618502788666131213697322783095070105623107215331596699973092056135872020481

abbrev F := ZMod PRIME

abbrev UInt8 := ZMod <| 2^8
abbrev UInt16 := ZMod <| 2^16
abbrev UInt32 := ZMod <| 2^32
abbrev UInt64 := ZMod <| 2^64
abbrev UInt128 := ZMod <| 2^128
abbrev UInt256 := ZMod <| 2^256

partial def SierraType.toQuote : SierraType → Q(Type)
  | .Felt252 => q(F)
  | .U8 => q(UInt8)
  | .U16 => q(UInt16)
  | .U32 => q(UInt32)
  | .U64 => q(UInt64)
  | .U128 => q(UInt128)
  | .U256 => q(UInt256)
  | .SierraBool => q(Bool)
  | .Addr => q(Sierra.Addr)
  | .RangeCheck => q(Nat)  -- TODO
  | .Enum []      => q(Unit)
  | .Enum [t]     => q($(t.toQuote))
  | .Enum (t::ts) => q($(t.toQuote) ⊕ $(toQuote (.Enum ts)))
  | .Struct []      => q(Unit)
  | .Struct [t]     => q($(t.toQuote))
  | .Struct (t::ts) => q($(t.toQuote) × $(toQuote (.Enum ts)))
  | .NonZero t => toQuote t -- TODO Maybe change to `{x : F // x ≠ 0}` somehow
  | .Box t => toQuote t
  | .Snapshot t => toQuote t
  | .Array t => q(List $(toQuote t))
  | .U128MulGuarantee => q(Unit) -- We don't store the guarantee in the type
  | .Pedersen => q(Nat)
  | .BuiltinCosts => q(Nat) -- TODO check whether we should run cairo to obtain the actual builtin costs
  | .GasBuiltin => q(Nat)

/-- A type holding the metadata that will not be contained in Sierra's `System` type -/
structure Metadata where
  (costs : Identifier → Nat)

notation "⟦" t "⟧" => SierraType.toQuote t

/-- A structure contining the branch-specific data for a libfunc -/
structure BranchData (inputTypes : List SierraType) where
  /-- The return types -/
  (outputTypes : List SierraType := [])
  /-- The condition associated with the branch -/
  (condition : OfInputs Q(Prop) 
    (List.map SierraType.toQuote <| inputTypes ++ outputTypes) := OfInputs.const <| q(True))
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
