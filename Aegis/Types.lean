import Aegis.Parser
import Aegis.ExprUtil
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
| SelfRef
  deriving Inhabited, Repr, ToExpr

/-- Checks whether a code for a Sierra type contains the self reference token. -/
partial def SierraType.containsSelfRef : SierraType → Bool
| .Enum fields
| .Struct fields => fields.any containsSelfRef
| .NonZero ty
| .Box ty
| .Snapshot ty
| .Array ty
| .Uninitialized ty
| .Nullable ty => ty.containsSelfRef
| .SelfRef => .true
| _ => .false

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


partial def SierraType.nonRefQuote : SierraType → Type
  | .Felt252 => F
  | .U8 => UInt8
  | .U16 => UInt16
  | .U32 => UInt32
  | .U64 => UInt64
  | .U128 => UInt128
  | .Addr => Sierra.Addr
  | .RangeCheck => Nat
  | .Enum []      => Empty
  | .Enum [t]     => t.nonRefQuote
  | .Enum (t::ts) => t.nonRefQuote ⊕ nonRefQuote (.Enum ts)
  | .Struct []      => Unit
  | .Struct [t]     => t.nonRefQuote
  | .Struct (t::ts) => t.nonRefQuote × nonRefQuote (.Struct ts)
  | .NonZero t => nonRefQuote t -- TODO Maybe change to `{x : F // x ≠ 0}` somehow
  | .Box t => nonRefQuote t
  | .Snapshot t => nonRefQuote t
  | .Array t => List <| nonRefQuote t
  | .U128MulGuarantee => Unit -- We don't store the guarantee in the type
  | .Pedersen => Nat
  | .BuiltinCosts => Nat -- TODO check whether we should run cairo to obtain the actual builtin costs
  | .GasBuiltin => Nat
  | .Bitwise => Nat
  | .Uninitialized _ => Unit -- Since we have no info on uninialized variables
  | .Nullable t => Option (nonRefQuote t)
  | .StorageBaseAddress => Sierra.StorageBaseAddress
  | .StorageAddress => Sierra.StorageAddress
  | .System => Sierra.System
  | .ContractAddress => Sierra.ContractAddress
  | .SelfRef => Unit  -- we should never reach this

/-- Because of restriction of nested types, this inlines all the constructors for the corresponding
Lean type formers. -/
inductive SierraType.Impl (self : SierraType) : SierraType → Type where
| enumHd             : Impl self t → Impl self (.Enum (t :: ts))
| enumTl             : Impl self (.Enum ts) → Impl self (.Enum (t :: ts))
| structNil          : Impl self (.Struct [])
| structCons         : Impl self t → Impl self (.Struct ts) → Impl self (.Struct (t :: ts))
| nonZero            : Impl self t → Impl self (.NonZero t)
| box                : Impl self t → Impl self (.Box t)
| snapshot           : Impl self t → Impl self (.Snapshot t)
| arrayNil           : Impl self (.Array t)
| arrayCons          : Impl self t → Impl self (.Array t) → Impl self (.Array t)
| nullable           : Impl self (.Nullable t)
| selfRef            : Impl self self → Impl self .SelfRef
| felt252            : F → Impl self .Felt252
| u8                 : UInt8 → Impl self .U8
| u16                : UInt16 → Impl self .U16
| u32                : UInt32 → Impl self .U32
| u64                : UInt64 → Impl self .U64
| u128               : UInt128 → Impl self .U128
| addr               : Sierra.Addr → Impl self .Addr
| rangeCheck         : ℕ → Impl self .RangeCheck
| u128MulGuarantee   : Impl self .U128MulGuarantee
| pedersen           : ℕ → Impl self .Pedersen
| builtinCosts       : ℕ → Impl self .BuiltinCosts
| gasBuiltin         : ℕ → Impl self .GasBuiltin
| bitwise            : ℕ → Impl self .Bitwise
| uninitialized      : Impl self (.Uninitialized _)
| nullableNone       : Impl self (.Nullable t)
| nullableSome       : Impl self t → Impl self (.Nullable t)
| storageBaseAddress : Sierra.StorageBaseAddress → Impl self .StorageBaseAddress
| storageAddress     : Sierra.StorageAddress → Impl self .StorageAddress
| system             : Sierra.System → Impl self .System
| contractAddress    : Sierra.ContractAddress → Impl self .ContractAddress

def SierraType.toQuote (t : SierraType) : Q(Type) :=
if t.containsSelfRef then q(Impl $t $t) else q(nonRefQuote $t)

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
