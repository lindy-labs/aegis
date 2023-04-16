import SierraLean.FuncDataUtil

open Qq

namespace Sierra

def Addr := Nat

namespace FuncData

def rename : FuncData where
  inputTypes := [q(Addr)]
  branches := [{ outputTypes := [q(Addr)],
                 refsChange := fun aρ rt => match aρ with
                  | [a, ρ] => (rt.insert ρ (rt.find! a)).erase a
                  | _ => panic! "Wrong number of arguments supplied to rename()" }]

def drop : FuncData where
  inputTypes := [q(Addr)]
  branches := [{ outputTypes := [],
                 refsChange := fun a rt => match a with
                  | [a] => rt.erase a
                  | _ => panic! "Wrong number of arguments supplied to drop()" }]

def dup : FuncData where
  inputTypes := [q(Addr)]
  branches := [{ outputTypes := [q(Addr), q(Addr)],
                 refsChange := fun aρ₁ρ₂ rt => match aρ₁ρ₂ with
                  | [a, ρ₁, ρ₂] => let fv := rt.find! a
                    ((rt.insert ρ₁ fv).insert ρ₂ fv).erase a
                  | _ => panic! "Wrong number of arguments supplied to dup()" }]

def store_temp : FuncData where
  inputTypes := [q(Addr)]
  branches := [{ outputTypes := [q(Addr)],
                 refsChange := fun aρ rt => match aρ with
                  | [a, ρ] => rt.insert ρ (rt.find! a)
                  | _ => panic! "Wrong number of arguments supplied to store_temp()" }]

-- Does nothing internally to Sierra
def branch_align : FuncData where

def jump : FuncData where

def controlFlowLibfuncs : Identifier → Option FuncData
  | .name "rename" [_]               => FuncData.rename
  | .name "drop" [_]                 => FuncData.drop
  | .name "store_temp" [_]           => FuncData.store_temp
  | .name "dup" [_]                  => FuncData.dup
  | .name "branch_align" []          => FuncData.branch_align
  | .name "jump" []                  => FuncData.jump
  | _                                => .none
