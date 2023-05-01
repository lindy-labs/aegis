import SierraLean.Parser
import SierraLean.FuncData
import SierraLean.FuncDataUtil

open Lean Expr Meta

namespace Sierra

open Classical

noncomputable section

def SierraType.val : SierraType → Type
  | .Felt252 => F
  | .U128 => UInt128
  | .SierraBool => Bool
  | .Addr => Sierra.Addr
  | .Enum fields => Σ i : Fin fields.length, (fields.get i).val
  | .Struct fields => ∀ i : Fin fields.length, (fields.get i).val
  | .NonZero τ => τ.val

notation "⟦ " τ " ⟧" => SierraType.val τ

structure BranchSignature where
  (outputs : List SierraType)

structure FuncSignature where
  (inputs : List SierraType)
  (branches : List BranchSignature)

def DMem := ℕ → Option (Σ τ : SierraType, ⟦ τ ⟧)

inductive StepResult (N : ℕ) where
  | Ok (pc : Fin N) (σ : DMem)
  | End (σ : DMem)
  | Error

structure IMem where
  (N : ℕ)
  (inst : Fin N → DMem → StepResult N)

structure Trace (imem : IMem) where
  (seq : ℕ → StepResult imem.N)
  (compat : ∀ n, seq (n+1) = match seq n with
    | .Ok pc σ => imem.inst pc σ
    | .End σ => .End σ
    | .Error => .Error)

def step_ok (imem : IMem)
  (pc : Fin imem.N) (σ : DMem)
  (pc' : Fin imem.N) (σ' : DMem) :=
  imem.inst pc σ = .Ok pc' σ'

def Trace.isOk {imem : IMem} (trace : Trace imem) :=
  ∀ N, ∃ pc : Fin imem.N, ∃ σ : DMem, trace.seq N = .Ok pc σ

def Trace.isError {imem : IMem} (trace : Trace imem) :=
  ∃ N, trace.seq N = .Error

def Trace.isInfinite {imem : IMem} (trace : Trace imem) :=
  ∀ n, match trace.seq n with
    | .Ok _ _ => True
    | _ => False

def Trace.isFrom {imem : IMem} (trace : Trace imem)
  (pc : Fin imem.N) (σ : DMem) :=
  trace.seq 0 = .Ok pc σ

def safeFrom (imem : IMem) (pc : Fin imem.N) (σ : DMem) :=
  ∀ trace : Trace imem, trace.isFrom pc σ → ¬ trace.isError

def convergeFrom (imem : IMem) (pc : Fin imem.N) (σ : DMem) :=
  ∀ trace : Trace imem, trace.isFrom pc σ → ¬ trace.isInfinite

theorem Trace.isOk_of_safeFrom_and_convergeFrom
  (imem : IMem) (pc : Fin imem.N) (σ : DMem)
  (h₁ : safeFrom imem pc σ)
  (h₂ : convergeFrom imem pc σ) :
  ∀ trace : Trace imem, trace.isFrom pc σ → trace.isOk := by
  sorry

def exceptError (N : ℕ) : Option (Fin N × DMem) → StepResult N
  | .some (pc, σ) => .Ok pc σ
  | .none => .Error

def incrPc (N : ℕ) (pc : Fin n) (σ : DMem) : Option (Fin N × DMem) :=
  let ⟨ pc, _ ⟩ := pc
  if p : (pc + 1) < N then
    some (⟨ pc + 1, p ⟩, σ)
  else none

def expectType (addr : ℕ) (τ : SierraType) (σ : DMem) : Option ⟦ τ ⟧ := do
  let ⟨ τ', v ⟩ ← σ addr
  if p : τ' = τ then (by
      rw [← p]
      exact some v
  ) else none

theorem expectType_val
  (addr : ℕ)
  (τ : SierraType)
  (v : ⟦ τ ⟧)
  (σ : DMem)
  (p : σ addr = some ⟨ τ, v ⟩) :
  expectType addr τ σ = some v := by
  simp [expectType, bind, p]

def expectCond : Bool → Option Unit
  | true => some ()
  | false => none

def inputs (R : Type) : List Type → Type
| []        => R
| (T :: Ts) => T → inputs R Ts

inductive Instruction where
  | BoolAnd (a b ρ : ℕ)
  | BoolXOR (a b ρ : ℕ)

inductive Params : ℕ → Type
  | nil : Params 0
  | cons (a : ℕ) (t : Params n) : Params (n+1)

def uncurried (T : Type) (n : ℕ) := Params n → T
def curried (T : Type) : ℕ → Type
  | 0 => T
  | n+1 => ℕ → curried T n
def currifyParams {T : Type} {n : ℕ} (f : uncurried T n) :
  curried T n := match n with
  | 0 => f .nil
  | _+1 => fun a => currifyParams fun x => f (.cons a x)

def sig : List SierraType → Type
  | [] => Bool
  | τ :: t => ⟦ τ ⟧ → sig t

def CheckT := DMem → Option Unit
def InstT (N : ℕ) := Fin N → DMem → StepResult N

def toChecked (σ : List SierraType) (f : sig σ) : uncurried CheckT σ.length :=
  match σ with
  | [] => fun _ _ => expectCond f
  | τ :: t => fun (.cons a t') σ => do
    let a ← expectType a τ σ
    toChecked t (f a) t' σ

section

def app
  (σ : DMem)
  (l : List (Σ n : ℕ, Σ τ : SierraType,
    Σ v : ⟦ τ ⟧, PLift (σ n = some ⟨ τ, v ⟩)))
  (f : sig (l.map fun x => x.2.1)) : Bool := match l with
  | [] => f
  | ⟨ _, _, v, _ ⟩ :: t => app σ t (f v)

def listToParams
  (σ : DMem)
  (l : List (Σ n : ℕ, Σ τ : SierraType,
    Σ v : ⟦ τ ⟧, PLift (σ n = some ⟨ τ, v ⟩))) :
  Params (l.map fun x => x.2.1).length := match l with
  | [] => .nil
  | ⟨ n, _ ⟩ :: t => .cons n <| listToParams σ t

theorem toChecked_val
  (σ : DMem)
  (l : List (Σ n : ℕ, Σ τ : SierraType,
    Σ v : ⟦ τ ⟧, PLift (σ n = some ⟨ τ, v ⟩)))
  (f : sig (l.map fun x => x.2.1)) :
  toChecked _ f (listToParams σ l) σ = expectCond (app σ l f) := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    let ⟨ n, τ, v, ⟨ p ⟩ ⟩ := x
    simp only [toChecked, listToParams, app,
      expectType_val n τ v σ p, bind]
    apply ih

#print cast

theorem t
  {α β : Type}
  {x : α}
  {h : α = β} :
  HEq x (h ▸ x) := by
  apply HEq.symm
  apply cast_heq  

theorem toChecked_val'
  (σ : DMem)
  (l : List (Σ n : ℕ, Σ τ : SierraType,
    Σ v : ⟦ τ ⟧, PLift (σ n = some ⟨ τ, v ⟩)))
  (f : sig (l.map fun x => x.2.1))
  (s : List SierraType)
  (x : Params s.length)
  (h : l.map (fun x => x.2.1) = s)
  (h' : x = (show (l.map fun x => x.2.1).length = s.length from h ▸ rfl)
    ▸ listToParams σ l) :
  toChecked s (h ▸ f) x σ = expectCond (app σ l f) := by
  rw [← toChecked_val σ l f]
  subst h
  rw [h']

end

def boolAnd_signature : List SierraType := 
  [ .SierraBool, .SierraBool, .SierraBool ]

def boolAnd_cond : sig boolAnd_signature :=
  fun (a b ρ : Bool) => ρ == (a && b)

def boolAnd_semantics' : uncurried CheckT boolAnd_signature.length :=
  toChecked boolAnd_signature boolAnd_cond

def jmp_semantics (N : ℕ) (offset : ℕ) (pc : Fin N) (σ : DMem) : StepResult N :=
  if p : pc + offset < N then
    .Ok ⟨ pc + offset, p ⟩ σ
  else
    .Error

def simple_check (N : ℕ) (s : List SierraType) (f : sig s) :
  uncurried (InstT N) s.length := fun x pc σ => exceptError N do
  (toChecked s f) x σ
  incrPc N pc σ

theorem simple_check_val
  (N : ℕ)
  (pc : Fin N)
  (σ : DMem)
  (l : List (Σ n : ℕ, Σ τ : SierraType,
    Σ v : ⟦ τ ⟧, PLift (σ n = some ⟨ τ, v ⟩)))
  (f : sig (l.map fun x => x.2.1)) :
  simple_check N (l.map fun x => x.2.1) f (listToParams σ l) pc σ
    = (exceptError N do
        expectCond (app σ l f)
        incrPc N pc σ)
  := by
  rw [← toChecked_val]
  rfl

theorem simple_check_val'
  (N : ℕ)
  (pc : Fin N)
  (σ : DMem)
  (s : List SierraType)
  (f : sig s)
  (x : Params s.length)
  (l : List (Σ n : ℕ, Σ τ : SierraType, Σ v : ⟦ τ ⟧, PLift (σ n = some ⟨ τ, v ⟩)))
  (h : s = l.map fun x => x.2.1)
  (h' : x = (show (l.map fun x => x.2.1).length = s.length from h ▸ rfl) ▸ listToParams σ l) :
  simple_check N s f x pc σ
    = (exceptError N do
        expectCond (app σ l (h ▸ f))
        incrPc N pc σ)
  := by
  rw [← simple_check_val N pc σ l (h ▸ f)]
  simp only [simple_check]
  subst h
  rw [h']

theorem simple_check_cond
  (N : ℕ)
  (pc : Fin N)
  (σ : DMem)
  (pc' : Fin N)
  (σ' : DMem)
  (s : List SierraType)
  (f : sig s)
  (x : Params s.length)
  (l : List (Σ n : ℕ, Σ τ : SierraType, Σ v : ⟦ τ ⟧, PLift (σ n = some ⟨ τ, v ⟩)))
  (h : s = l.map fun x => x.2.1)
  (h' : x = (show (l.map fun x => x.2.1).length = s.length from h ▸ rfl) ▸ listToParams σ l)
  (h'' : simple_check N s f x pc σ = .Ok pc' σ') :
  app σ l (h ▸ f) = true := by
  rw [simple_check_val' N pc σ s f x l h h'] at h''
  simp [bind, exceptError, expectCond] at h''
  cases p : app σ l (h ▸ f)
  simp [p] at h''
  rfl

def simple_semantics {N : ℕ} {σ : List SierraType} :
  sig σ → curried (InstT N) σ.length :=
  fun f => currifyParams <| simple_check N σ f

def std_interp (stmts : List Instruction) : IMem where
  N := stmts.length
  inst pc σ := match stmts.get pc with
    | .BoolAnd a b ρ =>
      simple_semantics boolAnd_cond a b ρ pc σ
    | _ => .Error

theorem incrPc_change
  (N : ℕ)
  (pc : Fin N)
  (σ : DMem)
  (pc' : Fin N)
  (σ' : DMem)
  (h : incrPc N pc σ = some (pc', σ') ) :
  (pc : ℕ) + 1 = pc' ∧ σ = σ' := by
  rw [incrPc] at h
  if p : pc + 1 < N then
    simp [p] at h
    exact ⟨ Fin.noConfusion h.1 id, h.2 ⟩
  else
    simp [p] at h

theorem simple_check_no_state_change
  (N : ℕ)
  (pc : Fin N)
  (σ : DMem)
  (pc' : Fin N)
  (σ' : DMem)
  (s : List SierraType)
  (f : sig s)
  (x : Params s.length)
  (h : simple_check N s f x pc σ = .Ok pc' σ' ) :
  (pc : ℕ) + 1 = pc' ∧ σ = σ' := by
  simp [simple_check, exceptError] at h
  match p : (do
    toChecked s f x σ
    incrPc N pc σ) with
  | none =>
    simp [p] at h
  | some (pc'', σ'') =>
    simp [p] at h
    simp [bind] at p
    rw [h.1, h.2] at p
    simp [incrPc] at p
    by_cases q : pc + 1 < N
      <;> simp [q] at p
    exact And.intro (Fin.noConfusion p.2.1 id) p.2.2

theorem eq₀ 
  (stmts : List Instruction)
  (pc : Fin stmts.length)
  (σ : DMem)
  (a b ρ : ℕ) :
  simple_semantics boolAnd_cond a b ρ pc σ =
    simple_check stmts.length _ boolAnd_cond
      (.cons a <| .cons b <| .cons ρ <| .nil)
      pc σ := by
  rfl

theorem interp_boolAnd
  (stmts : List Instruction)
  (pc : Fin stmts.length)
  (σ : DMem)
  (a b ρ : ℕ)
  (h : stmts.get pc = .BoolAnd a b ρ) :
  (std_interp stmts).inst pc σ =
    simple_semantics boolAnd_cond a b ρ pc σ := by
  simp only [std_interp, h]

theorem app_boolAnd_cond
  (σ : DMem)
  (a b ρ : ℕ)
  (a' b' ρ' : Bool)
  (h₁ : σ a = some ⟨ .SierraBool, a' ⟩)
  (h₂ : σ b = some ⟨ .SierraBool, b' ⟩)
  (h₃ : σ ρ = some ⟨ .SierraBool, ρ' ⟩) :
  app σ [ ⟨ _, _, _, ⟨ h₁ ⟩ ⟩, ⟨ _, _, _, ⟨ h₂ ⟩ ⟩, ⟨ _, _, _, ⟨ h₃ ⟩ ⟩ ] boolAnd_cond =
    boolAnd_cond a' b' ρ' := rfl

example
  (stmts : List Instruction)
  (pc : Fin stmts.length)
  (σ : DMem)
  (pc' : Fin stmts.length)
  (σ' : DMem)
  (a b ρ : ℕ)
  (h : stmts.get pc = .BoolAnd a b ρ)
  (h' : step_ok (std_interp stmts) pc σ pc' σ')
  (a' b' ρ' : Bool)
  (h₁ : σ a = some ⟨ .SierraBool, a' ⟩)
  (h₂ : σ b = some ⟨ .SierraBool, b' ⟩)
  (h₃ : σ ρ = some ⟨ .SierraBool, ρ' ⟩) : ρ' == (a' && b') := by
  simp only [step_ok, interp_boolAnd stmts pc σ a b ρ h, eq₀] at h'
  let l : List (Σ n : ℕ, Σ τ : SierraType, Σ v : ⟦ τ ⟧, PLift (σ n = some ⟨ τ, v ⟩)) :=
    [ ⟨ _, _, _, ⟨ h₁ ⟩ ⟩, ⟨ _, _, _, ⟨ h₂ ⟩ ⟩, ⟨ _, _, _, ⟨ h₃ ⟩ ⟩ ]
  have r := simple_check_cond stmts.length pc σ pc' σ' boolAnd_signature boolAnd_cond _ l rfl rfl h'
  rw [app_boolAnd_cond] at r
  cases q : boolAnd_cond a' b' ρ'
  simp [q] at r
  exact q
