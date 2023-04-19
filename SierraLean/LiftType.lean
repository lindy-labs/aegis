import SierraLean.Parser
import SierraLean.FuncData

open Lean Expr Meta Qq

namespace Sierra

inductive SierraType
| Felt252
| Enum (name : Identifier) (l : List SierraType)
  deriving Inhabited, Repr

partial def SierraType.val (τ : SierraType) : Type := match τ with
| .Felt252 => F
| .Enum _ l => Σ (i : Fin l.length), val (l.get i)

notation "⟦ " a " ⟧" => SierraType.val a

structure SierraSignature where
  (inputs : List SierraType)
  (outputs : List SierraType)
  deriving Inhabited, Repr

-- parameter : identifier / const / usertype / userfunc / libfunc
def buildTypeDefs (typedefs : List (Identifier × Identifier)) : Except String (HashMap Identifier SierraType) := do
  let mut acc := HashMap.empty
  for (name, ty) in typedefs do
    let v : SierraType ← go acc ty
    acc := HashMap.insert acc name v
  return acc
where go (acc : _) (ty : Identifier) : Except String SierraType :=
  match ty with
  | .name "felt252" [] => pure SierraType.Felt252
  | .name "Enum" (Parameter.identifier ident :: l) => do
    let l ← flip mapM l fun x => match x with
      | .identifier ident => pure ident
      | _ => throw "Expected Enum parameter to refer a to a type"
    pure <| SierraType.Enum ident (l.map acc.find!)
  | _ => throw "Unhandled"

def enumInitSig (typedefs : HashMap Identifier SierraType)
  (ty : Identifier) (variant : Int) : Except String SierraSignature := do
  let msg := "Expected variant to be 0 ≤ v < <number of variants>"
  let enumTy := typedefs.find! ty
  let variant ← match variant with
  | .ofNat n => pure n
  | _ => throw msg
  match enumTy with
  | .Enum _ l =>
    if p : variant < l.length then
      let ty := l.get ⟨ variant, p ⟩
      pure { inputs := [ty], outputs := [enumTy] }
    else throw msg
  | _ => throw "enum_init not referring to an enum type"

def buildFuncSignatures
  (typedefs : HashMap Identifier SierraType)
  (funcdefs : List (Identifier × Identifier)) : Except String (HashMap Identifier SierraSignature) := do
  let mut acc := HashMap.empty
  for (name, sig) in funcdefs do
    let v ← go sig
    acc := HashMap.insert acc name v
  return acc
where go (sig : Identifier) : Except String SierraSignature :=
  match sig with
    | .name "enum_init" args =>
      match args with
      | [Parameter.identifier ty, .const variant] =>
        enumInitSig typedefs ty variant
      | _ => throw "wrong arguments for enumInitSig"
    | _ => throw "unhandled"

--def SierraContext := ℕ → Option (Σ (τ : SierraType), ⟦ τ ⟧)
--def SierraState := List SierraContext

def test (code : String) : Except String Format := do
  let x ←  parseGrammar code
  let y ← buildTypeDefs x.typedefs
  let z ← buildFuncSignatures y x.libfuncs
  return z |> HashMap.toList |> List.map repr |> Format.join

def code02 := "type [0] = felt252;
 type [1] = Enum<foo, [0], [0]>;
 type [2] = Enum<bar, [1], [1]>;
 libfunc [0] = enum_init<[1], 1>;
 libfunc [1] = enum_init<[2], 1>;
 [0]([0]) -> ([1]);
 [1]([1]) -> ([2]);
 return([2]);
 foo@0([0]: [0]) -> ([2]);"
#eval test code02

