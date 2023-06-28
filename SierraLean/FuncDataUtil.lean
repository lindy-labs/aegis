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
| Bitwise
| Uninitialized (ty : SierraType)
| Nullable (ty : SierraType)
| StorageBaseAddress
| StorageAddress
| System
| ContractAddress
  deriving Inhabited, Repr

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

abbrev F := ZMod PRIME
abbrev UInt8 := ZMod <| 2^8
abbrev UInt16 := ZMod <| 2^16
abbrev UInt32 := ZMod <| 2^32
abbrev UInt64 := ZMod <| 2^64
abbrev UInt128 := ZMod <| 2^128
abbrev UInt256 := ZMod <| 2^256
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

partial def SierraType.toQuote : SierraType → Q(Type)
  | .Felt252 => q(F)
  | .U8 => q(UInt8)
  | .U16 => q(UInt16)
  | .U32 => q(UInt32)
  | .U64 => q(UInt64)
  | .U128 => q(UInt128)
  | .U256 => q(UInt256)
  | .Addr => q(Sierra.Addr)
  | .RangeCheck => q(Nat)  -- TODO
  | .Enum []      => q(Unit)
  | .Enum [t]     => t.toQuote
  | .Enum (t::ts) => q($(t.toQuote) ⊕ $(toQuote (.Enum ts)))
  | .Struct []      => q(Unit)
  | .Struct [t]     => t.toQuote
  | .Struct (t::ts) => q($(t.toQuote) × $(toQuote (.Struct ts)))
  | .NonZero t => toQuote t -- TODO Maybe change to `{x : F // x ≠ 0}` somehow
  | .Box t => toQuote t
  | .Snapshot t => toQuote t
  | .Array t => q(List $(toQuote t))
  | .U128MulGuarantee => q(Unit) -- We don't store the guarantee in the type
  | .Pedersen => q(Nat)
  | .BuiltinCosts => q(Nat) -- TODO check whether we should run cairo to obtain the actual builtin costs
  | .GasBuiltin => q(Nat)
  | .Bitwise => q(Nat)
  | .Uninitialized _ => q(Unit) -- Since we have no info on uninialized variables
  | .Nullable t => q(Option $(toQuote t))
  | .StorageBaseAddress => q(Sierra.StorageBaseAddress)
  | .StorageAddress => q(Sierra.StorageAddress)
  | .System => q(Sierra.System)
  | .ContractAddress => q(Sierra.ContractAddress)

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
