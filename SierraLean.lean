import SierraLean.Parser
import Mathlib.Data.ZMod.Basic

open Lean

namespace Sierra



abbrev RefTable := HashMap Nat FVarId

structure state
  (refFVars : HashMap Nat FVarId)
  (refTypes : HashMap Nat Expr)
  (conditions : List Expr)

class FuncData (name : String) (refsIn : List Nat) (refsOut : List Nat) where
  (refTableChange : RefTable → RefTable := id)
  (condition : Expr)
  (pcChange : Nat → Nat := (· + 1))

def spec_felt252_add (a b ρ : F): Prop := ρ = a + b


