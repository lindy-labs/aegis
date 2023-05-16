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

def step_noerr (imem : IMem) (pc : Fin imem.N) (σ : DMem) :=
  imem.inst pc σ ≠ .Error

--def Trace.isOk {imem : IMem} (trace : Trace imem) :=
--  ∀ N, ∃ pc : Fin imem.N, ∃ σ : DMem, trace.seq N = .Ok pc σ

def Trace.isError {imem : IMem} (trace : Trace imem) :=
  ∃ N, trace.seq N = .Error

def Trace.isInfinite {imem : IMem} (trace : Trace imem) :=
  ∀ n, match trace.seq n with
    | .Ok _ _ => True
    | _ => False

def Trace.converges {imem : IMem} (trace : Trace imem) :=
  ∃ n, ∃ σ, trace.seq n = .End σ

theorem Trace.step_ok (imem : IMem) (τ : Trace imem)
  {pc : Fin imem.N} {σ : DMem}
  (h₁ : τ.seq n = .Ok pc σ)
  : τ.seq (n+1) = imem.inst pc σ := by
  rw [τ.compat n, h₁]

def Trace.isFrom {imem : IMem} (trace : Trace imem)
  (pc : Fin imem.N) (σ : DMem) :=
  trace.seq 0 = .Ok pc σ

def safeFrom (imem : IMem) (pc : Fin imem.N) (σ : DMem) :=
  ∀ trace : Trace imem, trace.isFrom pc σ → ¬ trace.isError

def convergeFrom (imem : IMem) (pc : Fin imem.N) (σ : DMem) :=
  ∀ trace : Trace imem, trace.isFrom pc σ → ¬ trace.isInfinite

/-theorem Trace.isOk_of_safeFrom_and_convergeFrom
  (imem : IMem) (pc : Fin imem.N) (σ : DMem)
  (h₁ : safeFrom imem pc σ)
  (h₂ : convergeFrom imem pc σ) :
  ∀ trace : Trace imem, trace.isFrom pc σ → trace.isOk := by
  sorry-/

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

structure SimpleSpec where
  signature : List SierraType
  cond : sig signature

def simple_semantics {N : ℕ} (s : SimpleSpec)
  : curried (InstT N) s.signature.length :=
  currifyParams <| simple_check N s.signature s.cond

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
  {N : ℕ}
  {pc : Fin N}
  {σ : DMem}
  {s : List SierraType}
  {f : sig s}
  {x : Params s.length}
  (h : simple_check N s f x pc σ ≠ .Error) :
  ∃ (p : pc + 1 < N), simple_check N s f x pc σ
    = .Ok (⟨ pc + 1, p ⟩) σ := by
  simp [simple_check, exceptError] at h
  rw [simple_check, exceptError]
  match p : (do
    toChecked s f x σ
    incrPc N pc σ) with
  | none =>
    simp [p] at h
  | some (pc'', σ'') =>
    simp only [p]
    simp [bind] at p
    simp [incrPc] at p
    by_cases q : pc + 1 < N
      <;> simp [q] at p
    apply Exists.intro q
    rw [← p.2.1, ← p.2.2]

theorem simple_check_noerr_state {imem : IMem} (τ : Trace imem)
  (h : ¬ τ.isError)
  {n : ℕ}
  {pc : Fin imem.N}
  {σ : DMem}
  {s : List SierraType}
  {f : sig s}
  {x : Params s.length}
  (h' : τ.seq n = simple_check imem.N s f x pc σ)
  : ∃ (p : pc + 1 < imem.N), simple_check imem.N s f x pc σ
    = .Ok (⟨ pc + 1, p ⟩) σ := by
  apply simple_check_no_state_change
  intro h''
  apply h
  apply Exists.intro n
  rw [h']
  exact h''

theorem step_simple_check
  -- a valid trace
  (imem : IMem)
  (τ : Trace imem)
  (h : ¬ τ.isError)
  {n : ℕ}
  -- of which we know one state
  {pc : Fin imem.N}
  {σ : DMem}
  (h' : τ.seq n = .Ok pc σ)
  -- and that steps by a `simple_check`
  {s : List SierraType}
  {f : sig s}
  {x : Params s.length}
  (h'' : imem.inst pc σ = simple_check imem.N s f x pc σ)
  -- and we know more about that step
  (l : List (Σ n : ℕ, Σ τ : SierraType, Σ v : ⟦ τ ⟧, PLift (σ n = some ⟨ τ, v ⟩)))
  (h₁ : s = l.map fun x => x.2.1)
  (h₂ : x = (show (l.map fun x => x.2.1).length = s.length from h₁ ▸ rfl) ▸ listToParams σ l)
  : -- We know the next state (pc+1; no memory change)
    (∃ (p : pc + 1 < imem.N), τ.seq (n+1) = .Ok ⟨ pc + 1, p ⟩ σ)
    -- And we know the check is respected
    ∧ app σ l (h₁ ▸ f) = true := by
  have r := Trace.step_ok _ τ h'
  rw [h''] at r
  have p' := simple_check_noerr_state τ h r
  rw [r]
  apply And.intro (r ▸ p')
  apply simple_check_cond imem.N pc σ _ _ s f _ l h₁ h₂ p'.2

/-
# Now we specify our language
-/

def boolAnd_spec : SimpleSpec where
  signature := [ .SierraBool, .SierraBool, .SierraBool ]
  cond := fun (a b ρ : Bool) => ρ == (a && b)

def jmp_semantics (N : ℕ) (offset : ℕ) (pc : Fin N) (σ : DMem) : StepResult N :=
  if p : pc + offset < N then
    .Ok ⟨ pc + offset, p ⟩ σ
  else
    .Error

def std_interp (stmts : List Instruction) : IMem where
  N := stmts.length
  inst pc σ := match stmts.get pc with
    | .BoolAnd a b ρ =>
      simple_semantics boolAnd_spec a b ρ pc σ
    | _ => .Error

section

/- The theorems in this section should be automatically generated.
  They derive just from `SimpleSpec`s. -/

theorem interp_boolAnd_lemma₁
  (stmts : List Instruction)
  (pc : Fin stmts.length)
  (σ : DMem)
  (a b ρ : ℕ) :
  simple_semantics boolAnd_spec a b ρ pc σ =
    simple_check stmts.length _ boolAnd_spec.cond
      (.cons a <| .cons b <| .cons ρ <| .nil)
      pc σ := by
  rfl

theorem interp_boolAnd_lemma₂
  {stmts : List Instruction}
  {pc : Fin stmts.length}
  {a b ρ : ℕ}
  (h : stmts.get pc = .BoolAnd a b ρ)
  (σ : DMem)
  : (std_interp stmts).inst pc σ =
    simple_semantics boolAnd_spec a b ρ pc σ := by
  simp only [std_interp, h]

theorem interp_boolAnd
  {stmts : List Instruction}
  {pc : Fin stmts.length}
  {a b ρ : ℕ}
  (h : stmts.get pc = .BoolAnd a b ρ)
  (σ : DMem)
  : (std_interp stmts).inst pc σ =
    simple_check stmts.length _ boolAnd_spec.cond
      (.cons a <| .cons b <| .cons ρ <| .nil)
      pc σ := by
  rw [interp_boolAnd_lemma₂ h σ, interp_boolAnd_lemma₁]

end

theorem step_boolAnd
  -- a valid trace
  (stmts : List Instruction)
  (τ : Trace (std_interp stmts))
  (h : ¬ τ.isError)
  -- of which we know one state
  {n : ℕ}
  {pc : Fin stmts.length}
  {σ : DMem}
  (h' : τ.seq n = .Ok pc σ)
  -- and that steps by `boolAnd`
  {a b ρ : ℕ}
  (h'' : stmts.get pc = .BoolAnd a b ρ)
  {a' b' ρ' : Bool}
  (h₁ : σ a = some ⟨ .SierraBool, a' ⟩)
  (h₂ : σ b = some ⟨ .SierraBool, b' ⟩)
  (h₃ : σ ρ = some ⟨ .SierraBool, ρ' ⟩)
  : -- We know the next state (pc+1; no change in memory)
    (∃ (p : pc + 1 < stmts.length), τ.seq (n+1) = .Ok ⟨ pc + 1, p ⟩ σ)
    -- The state respects boolAnd
    ∧ ρ' == (a' && b') :=
  step_simple_check (std_interp stmts) τ h h'
    (interp_boolAnd h'' σ)
    [ ⟨ _, _, _, ⟨ h₁ ⟩ ⟩
    , ⟨ _, _, _, ⟨ h₂ ⟩ ⟩
    , ⟨ _, _, _, ⟨ h₃ ⟩ ⟩ ]
    rfl rfl
