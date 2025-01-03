import Aegis.Parser
import Aegis.ExprUtil
import Aegis.Macros
import Mathlib.Data.ZMod.Basic

open Lean Qq

namespace Sierra

/-- An inductive type containing "codes" for the types used in Sierra. The constructor `SelfRef`
is a placeholder for a *self reference* in a self referential (recursive) type. -/
inductive SierraType : Type
| Felt252
| U8
| U16
| U32
| U64
| U128
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
| Bitwise
| Uninitialized (ty : SierraType)
| Nullable (ty : SierraType)
| StorageBaseAddress
| StorageAddress
| System
| ContractAddress
| ConstNum (ty : SierraType) (val : ℤ)
| ConstStruct (ty : SierraType) (vals : List  SierraType)
/-- De-Bruĳn index for µ calculus -/
| Ref (n : ℕ)
/-- Anonymous μ binder -/
| Mu (ty : SierraType)
  deriving Inhabited, Repr, ToExpr

/-- Decrease all references above a certain threshold. -/
partial def decreaseRefs (above : Nat := 0) : SierraType → SierraType
| .Ref (.succ n) => .Ref n
| .Box ty => .Box <| decreaseRefs above ty
| .NonZero ty => .NonZero <| decreaseRefs above ty
| .Snapshot ty => .Snapshot <| decreaseRefs above ty
| .Array ty => .Array <| decreaseRefs above ty
| .Uninitialized ty => .Uninitialized <| decreaseRefs above ty
| .Nullable ty => .Nullable <| decreaseRefs above ty
| .Enum tys => .Enum (decreaseRefs above <$> tys)
| .Struct tys => .Struct (decreaseRefs above <$> tys)
| .Mu ty => .Mu (decreaseRefs (above + 1) ty)
| ty => ty

/-- Remove the outer µ-binders, leaving loose references! -/
def getMuBody : SierraType → SierraType
| .Mu ty => getMuBody ty
| ty => ty

partial def translate (raw : Std.HashMap Identifier Identifier) (ctx : List Identifier)
    (i : Identifier) : Except String (List Identifier × SierraType) := do
  match ctx.indexOf? i with
  | .some idx => .ok ([i], .Ref idx)
  | .none => match raw[i]? with
    | .some <| .name "felt252" [] .none => .ok ([], .Felt252)
    | .some <| .name "u8" [] .none => .ok ([], .U8)
    | .some <| .name "u16" [] .none => .ok ([], .U16)
    | .some <| .name "u32" [] .none => .ok ([], .U32)
    | .some <| .name "u64" [] .none => .ok ([], .U64)
    | .some <| .name "u128" [] .none => .ok ([], .U128)
    | .some <| .name "RangeCheck" [] .none => .ok ([], .RangeCheck)
    | .some <| .name "Pedersen" [] .none => .ok ([], .Pedersen)
    | .some <| .name "BuiltinCosts" [] .none => .ok ([], .BuiltinCosts)
    | .some <| .name "GasBuiltin" [] .none => .ok ([], .GasBuiltin)
    | .some <| .name "Bitwise" [] .none => .ok ([], .Bitwise)
    | .some <| .name "StorageBaseAddress" [] .none => .ok ([], .StorageBaseAddress)
    | .some <| .name "StorageAddress" [] .none => .ok ([], .StorageAddress)
    | .some <| .name "System" [] .none => .ok ([], .System)
    | .some <| .name "ContractAddress" [] .none => .ok ([], .ContractAddress)
    | .some <| .name "U128MulGuarantee" [] .none => .ok ([], .U128MulGuarantee)
    | .some <| .name "Box" [p] .none =>
      let .identifier ident := p
        | throw s!"Expected Box parameter {p} to refer to a type"
      let (lvs, ty) ← translate raw (i :: ctx) ident
      if lvs.contains i then .ok (lvs.removeAll [i], .Mu <| .Box ty)
      else .ok (lvs, .Box <| decreaseRefs 0 ty)
    | .some <| .name "NonZero" [p] .none =>
      let .identifier ident := p
        | throw s!"Expected NonZero parameter {p} to refer to a type"
      let (lvs, ty) ← translate raw (i :: ctx) ident
      if lvs.contains i then .ok (lvs.removeAll [i], .Mu <| .NonZero ty)
      else .ok (lvs, .NonZero <| decreaseRefs 0 ty)
    | .some <| .name "Snapshot" [p] .none =>
      let .identifier ident := p
        | throw s!"Expected Snapshot parameter {p} to refer to a type"
      let (lvs, ty) ← translate raw (i :: ctx) ident
      if lvs.contains i then .ok (lvs.removeAll [i], .Mu <| .Snapshot ty)
      else .ok (lvs, .Snapshot <| decreaseRefs 0 ty)
    | .some <| .name "Array" [p] .none =>
      let .identifier ident := p
        | throw s!"Expected Array parameter {p} to refer to a type"
      let (lvs, ty) ← translate raw (i :: ctx) ident
      if lvs.contains i then .ok (lvs.removeAll [i], .Mu <| .Array ty)
      else .ok (lvs, .Array <| decreaseRefs 0 ty)
    | .some <| .name "Uninitialized" [p] .none =>
      let .identifier ident := p
        | throw s!"Expected Uninitialized parameter {p} to refer to a type"
      let (lvs, ty) ← translate raw (i :: ctx) ident
      if lvs.contains i then .ok (lvs.removeAll [i], .Mu <| .Uninitialized ty)
      else .ok (lvs, .Uninitialized <| decreaseRefs 0 ty)
    | .some <| .name "Nullable" [p] .none =>
      let .identifier ident := p
        | throw s!"Expected Nullable parameter {p} to refer to a type"
      let (lvs, ty) ← translate raw (i :: ctx) ident
      if lvs.contains i then .ok (lvs.removeAll [i], .Mu <| .Nullable ty)
      else .ok (lvs, .Nullable <| decreaseRefs 0 ty)
    | .some <| .name "Enum" (_ :: ps) .none =>
      let idents ← flip mapM ps fun x => match x with
      | .identifier ident => pure ident
      | _ => throw "Expected Enum parameters to refer a to a type"
      let x ← idents.mapM <| translate raw (i :: ctx)
      let (lvs, tys) := x.unzip
      if lvs.flatten.contains i then .ok (lvs.flatten.removeAll [i], .Mu <| .Enum tys)
      else .ok (lvs.flatten, .Enum <| tys.map <| decreaseRefs 0)
    | .some <| .name "Struct" (_ :: ps) .none =>
      let idents ← flip mapM ps fun x => match x with
      | .identifier ident => pure ident
      | _ => throw "Expected Struct parameters to refer a to a type"
      let x ← idents.mapM <| translate raw (i :: ctx)
      let (lvs, tys) := x.unzip
      if lvs.flatten.contains i then .ok (lvs.flatten.removeAll [i], .Mu <| .Struct tys)
      else .ok (lvs.flatten, .Struct <| tys.map <| decreaseRefs 0)
    | .some <| .name "Const" (p :: ps) .none =>
      let ident ← match p with
      | .identifier ident => pure ident
      | _ => throw "Expected Const type to refer to a type"
      let (lvsty, ty) ← translate raw (i :: ctx) ident
      match ty with
      | .Struct _ =>
        let idents ← flip mapM ps fun x => match x with
        | .identifier ident => pure ident
        | _ => throw "Expected Const parameters to refer a to a type"
        let x ← idents.mapM <| translate raw (i :: ident :: ctx)  -- really add `ident`?
        let (lvs, tys) := x.unzip
        .ok (lvs.flatten, .ConstStruct ty tys)
      | .U8 | .U16 | .U32 | .U64 | .U128 | .Felt252 =>
        let num : ℤ ← match ps with
        | [.const n] => pure n
        | _ => throw "parameter to numerical constant type must be a numeral"
        .ok (lvsty, .ConstNum ty num)  -- really `lvsty`?
      | _ => throw "type not able to form constant types"
    | _ => throw s!"Type not translatable: {i}"

def buildTypeDefs (typedefs : List (Identifier × Identifier)) :
    Except String (Std.HashMap Identifier SierraType) := do
  let idents := typedefs.map (·.1)
  let x ← idents.mapM <| translate (.ofList typedefs) []
  .ok <| .ofList <| idents.zip <| x.map (·.2)

abbrev RefTable := Std.HashMap Nat FVarId

instance : ToString RefTable where toString x := toString $ repr x.toList

def PRIME :=
  3618502788666131213697322783095070105623107215331596699973092056135872020481

def BASE_MOD :=
  3618502788666131106986593281521497120414687020801267626233049500247285300992

def ADDRESS_MOD :=
  3618502788666131106986593281521497120414687020801267626233049500247285301248

def CONTRACT_ADDRESS_MOD :=
  3618502788666131106986593281521497120414687020801267626233049500247285301248

def U128_MOD :=
  340282366920938463463374607431768211456

def U64_MOD :=
  18446744073709551616

def U32_MOD :=
  4294967296

def U16_MOD :=
  65536

def U8_MOD :=
  256

abbrev F := ZMod PRIME
abbrev UInt8 := BitVec 3
abbrev UInt16 := BitVec 4
abbrev UInt32 := BitVec 5
abbrev UInt64 := BitVec 6
abbrev UInt128 := BitVec 7
abbrev StorageBaseAddress := ZMod BASE_MOD
abbrev StorageAddress := ZMod ADDRESS_MOD
abbrev ContractAddress := ZMod CONTRACT_ADDRESS_MOD

structure ContractState where
  (class_hash : F)
  (storage :  StorageAddress → F)
  (nonce : ℕ)

structure EventData where
  (contract : ContractAddress)
  (keys : List F)
  (data : List F)

structure System where
  (contracts : F → ContractState)  -- TODO check if the domain is really `F`
  (events : List EventData)

def System.emitEvent (s : System) (e : EventData): System := { s with events := s.events ++ [e] }

def System.writeStorage (s : System) (contract : F) (addr : StorageAddress) (val : F) : System :=
  { s with contracts := Function.update s.contracts contract <|
             { s.contracts contract with storage := Function.update (s.contracts contract).storage addr val } }

@[semireducible]
def SierraType.toType (ctx : List Type := []) : SierraType → Type
  | .Felt252 => F
  | .U8 => UInt8
  | .U16 => UInt16
  | .U32 => UInt32
  | .U64 => UInt64
  | .U128 => UInt128
  | .RangeCheck => Nat  -- TODO
  | .Enum []      => Unit
  | .Enum [t]     => toType ctx t
  | .Enum (t::ts) => (toType ctx t) ⊕ (toType ctx (.Enum ts))
  | .Struct []      => Unit
  | .Struct [t]     => toType ctx t
  | .Struct (t::ts) => (toType ctx t) × (toType ctx (.Struct ts))
  | .NonZero t => toType ctx t -- TODO Maybe change to `{x : F // x ≠ 0}` somehow
  | .Box _ => Nat
  | .Snapshot t => toType ctx t
  | .Array t => List (toType ctx t)
  | .U128MulGuarantee => Unit -- We don't store the guarantee in the type
  | .Pedersen => Nat
  | .BuiltinCosts => Nat -- TODO check whether we should run cairo to obtain the actual builtin costs
  | .GasBuiltin => Nat
  | .Bitwise => Nat
  | .Uninitialized t => toType ctx t -- Since we have no info on uninialized variables
  | .Nullable t => Option (toType ctx t)
  | .StorageBaseAddress => Sierra.StorageBaseAddress
  | .StorageAddress => Sierra.StorageAddress
  | .System => Sierra.System
  | .ContractAddress => Sierra.ContractAddress
  | .ConstNum _ _ => Unit  -- no runtime information in const types
  | .ConstStruct _ _ => Unit  -- no runtime information in const types
  | .Ref n => ctx.get! n  -- TODO check whether `drop n` is right
  | .Mu t => toType (toType ctx t :: ctx) t -- ???

partial def SierraType.toQuote (ctx : List SierraType := []) : SierraType → Q(Type)
  | .Felt252 => q(F)
  | .U8 => q(UInt8)
  | .U16 => q(UInt16)
  | .U32 => q(UInt32)
  | .U64 => q(UInt64)
  | .U128 => q(UInt128)
  | .RangeCheck => q(Nat)  -- TODO
  | .Enum []      => q(Unit)
  | .Enum [t]     => toQuote ctx t
  | .Enum (t::ts) => q($(toQuote ctx t) ⊕ $(toQuote ctx (.Enum ts)))
  | .Struct []      => q(Unit)
  | .Struct [t]     => toQuote ctx t
  | .Struct (t::ts) => q($(toQuote ctx t) × $(toQuote ctx (.Struct ts)))
  | .NonZero t => toQuote ctx t -- TODO Maybe change to `{x : F // x ≠ 0}` somehow
  | .Box _ => q(Nat)
  | .Snapshot t => toQuote ctx t
  | .Array t => q(List $(toQuote ctx t))
  | .U128MulGuarantee => q(Unit) -- We don't store the guarantee in the type
  | .Pedersen => q(Nat)
  | .BuiltinCosts => q(Nat) -- TODO check whether we should run cairo to obtain the actual builtin costs
  | .GasBuiltin => q(Nat)
  | .Bitwise => q(Nat)
  | .Uninitialized t => toQuote ctx t -- Since we have no info on uninialized variables
  | .Nullable t => q(Option $(toQuote ctx t))
  | .StorageBaseAddress => q(Sierra.StorageBaseAddress)
  | .StorageAddress => q(Sierra.StorageAddress)
  | .System => q(Sierra.System)
  | .ContractAddress => q(Sierra.ContractAddress)
  | .ConstNum _ _ => q(Unit)
  | .ConstStruct _ _ => q(Unit)
  | .Ref n => toQuote (ctx.drop n) (ctx.get! n)  -- TODO check whether `drop n` is right
  | .Mu t => toQuote (t :: ctx) t

notation "⟦" t "⟧" => SierraType.toQuote [] t

def SierraType.BlockInfo : SierraType :=
.Struct [ .U64  -- block number
        , .U64  -- block timestamp
        , .ContractAddress ]  -- sequencer address

def SierraType.TxInfo : SierraType :=
.Struct [ .Felt252  -- transaction version
        , .ContractAddress  -- the account contract from which this tx originates
        , .U128  -- max fee
        , .Struct [.Snapshot <| .Array .Felt252] -- signature of the tx
        , .Felt252  -- transaction hash
        , .Felt252  -- identifier of the chain
        , .Felt252  -- nonce
        ]

def SierraType.ExecutionInfo : SierraType :=
.Struct [ .Box .BlockInfo
        , .Box .TxInfo
        , .ContractAddress  -- caller address
        , .ContractAddress  -- contract address
        , .Felt252  -- entry point selector
        ]

def SierraType.ResourceBounds : SierraType :=
.Struct [ .Felt252  -- resource
        , .U64  -- max amount
        , .U128  -- max price per unit
        ]

def SierraType.V2TxInfo : SierraType :=
.Struct [ .Felt252  -- transaction version
        , .ContractAddress  -- the account contract from which this tx originates
        , .U128  -- max fee
        , .Struct [.Snapshot <| .Array .Felt252] -- signature of the tx
        , .Felt252  -- transaction hash
        , .Felt252  -- identifier of the chain
        , .Felt252  -- nonce
        , .Struct [.Snapshot <| .Array .ResourceBounds] -- resource bounds
        , .U128  -- tip
        , .Struct [.Snapshot <| .Array .Felt252] -- paymaster data
        , .U32  -- data availability for nonce
        , .U32  -- data availability for fee
        , .Struct [.Snapshot <| .Array .Felt252] -- account deployment data
        ]

def SierraType.V2ExecutionInfo : SierraType :=
.Struct [ .Box .BlockInfo
        , .Box .V2TxInfo
        , .ContractAddress  -- caller address
        , .ContractAddress  -- contract address
        , .Felt252  -- entry point selector
        ]

/-- A type holding the metadata that will not be contained in Sierra's `System` type -/
structure Metadata : Type where
  (pedersen : F → F → F)  -- TODO this dummy should be replaced by a real reimplementation
  (costs : Identifier → Nat)
  (callerAddress : ContractAddress)
  (contractAddress : ContractAddress)
  (entryPointSelector : F)
  (txVersion : F)
  (txContract : ContractAddress)
  (txMaxFee : UInt128)
  (txSignature : List F)
  (txHash : F)
  (txChainIdentifier : F)
  (txNonce : F)
  (txResourceBounds : List (F × UInt64 × UInt128))
  (txTip : UInt128)
  (txPaymasterData : List F)
  (txDataAvailabilityNonce : UInt32)
  (txDataAvailabilityFee : UInt32)
  (txAccountDeploymentData : List F)
  (blockNumber : UInt64)
  (blockTimestamp : UInt64)
  (sequencerAddress : ContractAddress)
  /-- Contains the contents of the `n`th box for the sierra type `t` -/
  (boxHeap : (t : SierraType) → (n : Nat) → Option t.toType)
  /-- Returns the result for `call_contract_syscall` for a given contract, selector, call data,
    caller, and system state. The result consists of the actual return value as well as the
    resulting system state. -/
  (callResult : (c : ContractAddress) → (f : F) → (d : List F) → (caller : ContractAddress)
    → System → List F × System)

/-- A structure contining the branch-specific data for a libfunc -/
structure BranchData (inputTypes : List SierraType) where
  /-- The return types -/
  (outputTypes : List SierraType := [])
  /-- The condition associated with the branch -/
  (condition : OfInputs Q(Prop)
    (List.map SierraType.toQuote <| inputTypes ++ outputTypes) := OfInputs.const <| q(True))

instance : Inhabited (BranchData inputTypes) := ⟨{ }⟩

/-- A structure containing all necessary data to process a libfunc -/
structure FuncData where
  /-- The types of the arguments, empty by default -/
  (inputTypes : List SierraType := [])
  /-- The list of branches, one branch by default -/
  (branches : List (BranchData inputTypes) := [{ }])

def FuncData.modifyConditions (fd : FuncData) (f : Expr → Expr) : FuncData where
  inputTypes := fd.inputTypes
  branches := fd.branches.map fun bd =>
    { bd with condition := OfInputs.map f bd.condition }

instance : Inhabited FuncData := ⟨{ }⟩

/-- A structure to contain the information on the implicit that's added to the wrapper call
for a registered contract call -/
structure ContractCallImplicit where
  (type : SierraType)
  (pre : Expr)
  (post : Expr)

/-- A structure containing the data necessary to pin a contract call to a specific Sierra id -/
structure ContractCallData where
  (ident : Identifier)
  (contractAddress : Q(ContractAddress))
  (selector : Q(F))
  (implicits : List ContractCallImplicit)

instance : Inhabited ContractCallData := ⟨default, default, default, []⟩

/- Make `Identifier` and `Parameter` quotable. -/
mutual

partial def Parameter.quote : Parameter → Q(Parameter)
| .identifier i => q(.identifier $(Identifier.quote i))
| .const n => q(.const $n)
| .usertype i => q(.usertype $(Identifier.quote i))
| .userfunc i => q(.userfunc $(Identifier.quote i))
| .libfunc i => q(.libfunc $(Identifier.quote i))
| .tuple ps => ParameterList.quote ps
| .placeholder => q(.placeholder)

partial def ParameterList.quote : List Parameter → Q(List Parameter)
| [] => q([])
| p::ps => q($(Parameter.quote p) :: $(ParameterList.quote ps))

partial def Identifier.quote : Identifier → Q(Identifier)
| .ref n => q(.ref $n)
| .name n ps tl => q(.name $n $(ParameterList.quote ps) $(OptionIdentifier.quote tl))

partial def OptionIdentifier.quote : Option Identifier → Q(Option Identifier)
| .none => q(.none)
| .some i => q(.some $(Identifier.quote i))

end

instance : ToExpr Identifier := ⟨Identifier.quote, q(Identifier)⟩
instance : ToExpr Parameter := ⟨Parameter.quote, q(Parameter)⟩
