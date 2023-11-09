import Aegis.Parser
import Aegis.ExprUtil
import Aegis.Macros
import Mathlib.Data.ZMod.Basic

open Lean Qq

namespace Sierra

def Addr := Nat

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
/-- De-Bruĳn index for µ calculus -/
| Ref (n : ℕ)
/-- Anonymous μ binder -/
| Mu (ty : SierraType)
  deriving Inhabited, Repr, ToExpr

partial def decreaseRefs : SierraType → SierraType
| .Ref (.succ n) => .Ref n
| .Box ty => .Box <| decreaseRefs ty
| .NonZero ty => .NonZero <| decreaseRefs ty
| .Snapshot ty => .Snapshot <| decreaseRefs ty
| .Array ty => .Array <| decreaseRefs ty
| .Uninitialized ty => .Uninitialized <| decreaseRefs ty
| .Nullable ty => .Nullable <| decreaseRefs ty
| .Enum tys => .Enum (decreaseRefs <$> tys)
| .Struct tys => .Struct (decreaseRefs <$> tys)
| ty => ty

partial def translate (raw : HashMap Identifier Identifier) (ctx : List Identifier)
    (i : Identifier) : Except String (List Identifier × SierraType) := do
  match ctx.indexOf? i with
  | .some idx => .ok ([i], .Ref idx)
  | .none => match raw.find? i with
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
    | .some <| .name "Box" [p] .none =>
      let .identifier ident := p
        | throw s!"Expected Box parameter {p} to refer to a type"
      let (lvs, ty) ← translate raw (i :: ctx) ident
      if lvs.contains i then .ok (lvs.removeAll [i], .Mu <| .Box ty)
      else .ok (lvs, .Box <| decreaseRefs ty)
    | .some <| .name "NonZero" [p] .none =>
      let .identifier ident := p
        | throw s!"Expected NonZero parameter {p} to refer to a type"
      let (lvs, ty) ← translate raw (i :: ctx) ident
      if lvs.contains i then .ok (lvs.removeAll [i], .Mu <| .NonZero ty)
      else .ok (lvs, .NonZero <| decreaseRefs ty)
    | .some <| .name "Snapshot" [p] .none =>
      let .identifier ident := p
        | throw s!"Expected Snapshot parameter {p} to refer to a type"
      let (lvs, ty) ← translate raw (i :: ctx) ident
      if lvs.contains i then .ok (lvs.removeAll [i], .Mu <| .Snapshot ty)
      else .ok (lvs, .Snapshot <| decreaseRefs ty)
    | .some <| .name "Array" [p] .none =>
      let .identifier ident := p
        | throw s!"Expected Array parameter {p} to refer to a type"
      let (lvs, ty) ← translate raw (i :: ctx) ident
      if lvs.contains i then .ok (lvs.removeAll [i], .Mu <| .Array ty)
      else .ok (lvs, .Array <| decreaseRefs ty)
    | .some <| .name "Uninitialized" [p] .none =>
      let .identifier ident := p
        | throw s!"Expected Uninitialized parameter {p} to refer to a type"
      let (lvs, ty) ← translate raw (i :: ctx) ident
      if lvs.contains i then .ok (lvs.removeAll [i], .Mu <| .Uninitialized ty)
      else .ok (lvs, .Uninitialized <| decreaseRefs ty)
    | .some <| .name "Nullable" [p] .none =>
      let .identifier ident := p
        | throw s!"Expected Nullable parameter {p} to refer to a type"
      let (lvs, ty) ← translate raw (i :: ctx) ident
      if lvs.contains i then .ok (lvs.removeAll [i], .Mu <| .Nullable ty)
      else .ok (lvs, .Nullable <| decreaseRefs ty)
    | .some <| .name "Enum" (_ :: ps) .none =>
      let idents ← flip mapM ps fun x => match x with
      | .identifier ident => pure ident
      | _ => throw "Expected Enum parameter to refer a to a type"
      let x ← idents.mapM <| translate raw (i :: ctx)
      let (lvs, tys) := x.unzip
      if lvs.join.contains i then .ok (lvs.join.removeAll [i], .Mu <| .Enum tys)
      else .ok (lvs.join, .Enum <| tys.map decreaseRefs)
    | .some <| .name "Struct" (_ :: ps) .none =>
      let idents ← flip mapM ps fun x => match x with
      | .identifier ident => pure ident
      | _ => throw "Expected Struct parameter to refer a to a type"
      let x ← idents.mapM <| translate raw (i :: ctx)
      let (lvs, tys) := x.unzip
      if lvs.join.contains i then .ok (lvs.join.removeAll [i], .Mu <| .Struct tys)
      else .ok (lvs.join, .Struct <| tys.map decreaseRefs)
    | _ => throw s!"Type not translatable: {i}"

def buildTypeDefs (typedefs : List (Identifier × Identifier)) :
    Except String (HashMap Identifier SierraType) := do
  let idents := typedefs.map (·.1)
  let x ← idents.mapM <| translate (.ofList typedefs) []
  .ok <| HashMap.ofList <| idents.zip <| x.map (·.2)

abbrev RefTable := HashMap Nat FVarId

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
abbrev UInt8 := ZMod U8_MOD
abbrev UInt16 := ZMod U16_MOD
abbrev UInt32 := ZMod U32_MOD
abbrev UInt64 := ZMod U64_MOD
abbrev UInt128 := ZMod U128_MOD
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

/- Because of restriction of nested types, this inlines all the constructors for the corresponding
Lean type formers. -/
inductive SierraType.Impl : List SierraType → SierraType → Type where
| enumHd             : Impl ctx t → Impl ctx (.Enum (t :: ts))
| enumTl             : Impl ctx (.Enum ts) → Impl ctx (.Enum (t :: ts))
| structNil          : Impl ctx (.Struct [])
| structCons         : Impl ctx t → Impl ctx (.Struct ts) → Impl ctx (.Struct (t :: ts))
| nonZero            : Impl ctx t → Impl ctx (.NonZero t)
| box                : Impl ctx t → Impl ctx (.Box t)
| snapshot           : Impl ctx t → Impl ctx (.Snapshot t)
| arrayNil           : Impl ctx (.Array t)
| arrayCons          : Impl ctx t → Impl ctx (.Array t) → Impl ctx (.Array t)
| nullable           : Impl ctx (.Nullable t)
| felt252            : F → Impl ctx .Felt252
| u8                 : UInt8 → Impl ctx .U8
| u16                : UInt16 → Impl ctx .U16
| u32                : UInt32 → Impl ctx .U32
| u64                : UInt64 → Impl ctx .U64
| u128               : UInt128 → Impl ctx .U128
| rangeCheck         : ℕ → Impl ctx .RangeCheck
| u128MulGuarantee   : Impl ctx .U128MulGuarantee
| pedersen           : ℕ → Impl ctx .Pedersen
| builtinCosts       : ℕ → Impl ctx .BuiltinCosts
| gasBuiltin         : ℕ → Impl ctx .GasBuiltin
| bitwise            : ℕ → Impl ctx .Bitwise
| uninitialized      : Impl ctx (.Uninitialized _)
| nullableNone       : Impl ctx (.Nullable t)
| nullableSome       : Impl ctx t → Impl ctx (.Nullable t)
| storageBaseAddress : Sierra.StorageBaseAddress → Impl ctx .StorageBaseAddress
| storageAddress     : Sierra.StorageAddress → Impl ctx .StorageAddress
| system             : Sierra.System → Impl ctx .System
| contractAddress    : Sierra.ContractAddress → Impl ctx .ContractAddress
/-- This is the unrolling step of the recursive types. -/
| ref                : ∀ (k : Fin ctx.length), Impl (ctx.drop k) (ctx.get k) → Impl ctx (.Ref k)
/-- Interpret the μ binders by extending the context -/
| mu                 : Impl (t :: ctx) t → Impl ctx (.Mu t)

def SierraType.toType : SierraType → Type
  | .Felt252 => F
  | .U8 => UInt8
  | .U16 => UInt16
  | .U32 => UInt32
  | .U64 => UInt64
  | .U128 => UInt128
  | .RangeCheck => Nat
  | .Enum []      => Empty
  | .Enum [t]     => t.toType
  | .Enum (t::ts) => t.toType ⊕ toType (.Enum ts)
  | .Struct []      => Unit
  | .Struct [t]     => t.toType
  | .Struct (t::ts) => t.toType × toType (.Struct ts)
  | .NonZero t => toType t -- TODO Maybe change to `{x : F // x ≠ 0}` somehow
  | .Box t => toType t
  | .Snapshot t => toType t
  | .Array t => List <| toType t
  | .U128MulGuarantee => Unit -- We don't store the guarantee in the type
  | .Pedersen => Nat
  | .BuiltinCosts => Nat -- TODO check whether we should run cairo to obtain the actual builtin costs
  | .GasBuiltin => Nat
  | .Bitwise => Nat
  | .Uninitialized _ => Unit -- Since we have no info on uninialized variables
  | .Nullable t => Option (toType t)
  | .StorageBaseAddress => Sierra.StorageBaseAddress
  | .StorageAddress => Sierra.StorageAddress
  | .System => Sierra.System
  | .ContractAddress => Sierra.ContractAddress
  | .Mu t => SierraType.Impl [t] t
  | .Ref _ => panic "encountered SierraType.Ref outside of a Mu binder!"  -- should never reach this

def SierraType.toQuote (t : SierraType) : Q(Type) := q(SierraType.toType $t)

notation "⟦" t "⟧" => SierraType.toQuote t

def SierraType.BlockInfo : SierraType :=
.Struct [ .U64  -- block number
        , .U64  -- block timestamp
        , .ContractAddress ]  -- sequencer address

def SierraType.TxInfo : SierraType :=
.Struct [ .Felt252  -- transaction version
        , .ContractAddress  -- the account contract from which this tx originates
        , .U128  -- max fee
        , .Snapshot <| .Array .Felt252 -- signature of the tx
        , .Felt252  -- transaction hash
        , .Felt252  -- identifier of the chain
        , .Felt252  -- nonce
        ]

def SierraType.ExecutionInfo : SierraType :=
.Struct [ .BlockInfo
        , .TxInfo
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
  (blockNumber : UInt64)
  (blockTimestamp : UInt64)
  (sequencerAddress : ContractAddress)

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

def FuncData.modifyConditions (fd : FuncData) (f : Expr → Expr) : FuncData where
  inputTypes := fd.inputTypes
  branches := fd.branches.map fun bd =>
    { bd with condition := OfInputs.map f bd.condition }

instance : Inhabited FuncData := ⟨{ }⟩
