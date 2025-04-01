import Lean.Meta.AppBuilder
import Mathlib.Lean.Expr.Basic
import Qq

open Lean Qq Meta

def List.enumFin (xs : List α) : List (Fin xs.length × α) :=
match xs with
| []      => []
| x :: xs => ((0 : Fin (length xs + 1)), x) :: xs.enumFin.map fun x => (Fin.succ x.1, x.2)

def Lean.Expr.getFVars (e : Expr) : Array FVarId := (Lean.CollectFVars.main e { }).fvarIds

def Lean.Expr.or? (p : Expr) := p.app2? ``And

def Lean.Expr.tuple? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
e.app4? ``Prod.mk

namespace Sierra

def Expr.mkAnds : List Expr → Expr
| []        => mkConst ``True
| [e]       => e
| (e :: es) => mkApp (mkApp (mkConst ``And) e) (mkAnds es)

/-- Build the disjunction of a list of expressions -/
def Expr.mkOrs : List Expr → Expr
| []        => mkConst ``False
| [e]       => e
| (e :: es) => mkApp (mkApp (mkConst ``Or) e) <| mkOrs es

def Expr.mkEq (type : Expr) (lhs rhs : Expr) : Expr :=
mkAppN (mkConst `Eq [levelOne]) #[type, lhs, rhs]

def mkEqM (lhs rhs : Expr) : MetaM Expr := mkAppM ``Eq #[lhs, rhs]

/-- A tree to contain expressions to be composed with `And` and `Or`.
If we want to avoid trees, this has to be replaced by some graph structure in the future. -/
inductive AndOrTree
| nil  : AndOrTree
| cons : Expr → List AndOrTree → AndOrTree
deriving Inhabited, Repr

instance : ToString AndOrTree where toString x := toString $ repr x

partial def AndOrTree.format (es : AndOrTree) : MetaM Format :=
match es with
| .nil => pure "[]"
| .cons e es => do
  let e ← ppExpr e
  let es : List Format ← es.mapM fun e => e.format
  let es := es.format
  return e ++ " ∧ " ++ es

def AndOrTree.isNil : AndOrTree → Bool
| nil      => true
| cons _ _ => false

/-- Checks if an `AndOrTree` only consists of trivial nodes -/
partial def AndOrTree.isTrivial : AndOrTree → Bool
| nil                       => true
| cons (.const ``True _) ts => ts.all AndOrTree.isTrivial
| _                         => false

/-- Compile an `AndOrTree` down to a single expression -/
partial def AndOrTree.toExpr : AndOrTree → Expr
| nil       => mkConst ``True
| cons e [] => e
| cons (.const ``True _) ts => Expr.mkOrs <| (AndOrTree.toExpr <$> ts)
| cons e ts =>
   if ts.all (·.isTrivial) then e
   else mkApp (mkApp (mkConst ``And) e) <| Expr.mkOrs <| (AndOrTree.toExpr <$> ts)

/-- Filter an `AndOrTree` by a boolean predicate on expressions -/
partial def AndOrTree.filter (p : Expr → Bool) : AndOrTree → AndOrTree
| nil                     => nil
| cons e []               => if p e then cons e [] else nil
| cons e [c@(cons e' ts)] => if p e' then cons e [AndOrTree.filter p c]
                             else cons e ts
| cons e (nil :: ts)         => AndOrTree.filter p <| cons e ts
| cons e (cons e' ts' :: ts) => if p e' then cons e (cons e' ts' :: AndOrTree.filter p <$> ts)
                                else AndOrTree.filter p <| cons e ts

/-- Map an expression transformation on an `AndOrTree` -/
partial def AndOrTree.map (f : Expr → Expr) : AndOrTree → AndOrTree
| nil       => nil
| cons e ts => cons (f e) (ts.map <| AndOrTree.map f)

/-- Append at leftmost point, TODO delete -/
def AndOrTree.append (t : AndOrTree) (e : Expr) : AndOrTree :=
  match t with
  | nil               => cons e []
  | cons e' []        => cons e' [cons e []]
  | cons e' (t :: ts) => cons e' (t.append e :: ts)

/-- Apply a substitution to an `AndOrTree` -/
def AndOrTree.applySubst (t : AndOrTree) (s : FVarSubst) := t.map s.apply

/-- Splits conjunctions apperaing in nodes -/
partial def AndOrTree.normalize (t : AndOrTree) : AndOrTree :=
  match t with
  | nil => nil
  | cons e ts =>
    match e.and? with
    | .some (l, r) => normalize <| .cons l [.cons r ts]
    | .none => .cons e (normalize <$> ts)

partial def AndOrTree.separateTupleEqs (t : AndOrTree) : AndOrTree :=
  match t with
  | nil => nil
  | cons e ts =>
    match e.eq? with
    | .some (_, lhs, rhs) =>
      match lhs.tuple?, rhs.tuple? with
      | .some ⟨α, β, x₁, y₁⟩, .some ⟨_, _, x₂, y₂⟩ =>
        let fstEq := Sierra.Expr.mkEq α x₁ x₂
        let sndEq := Sierra.Expr.mkEq β y₁ y₂
        .cons fstEq [AndOrTree.separateTupleEqs (AndOrTree.cons sndEq ts)]
      | .some ⟨α, β, x, y⟩, _ =>
        let fstEq := Sierra.Expr.mkEq α x (Expr.proj `Prod 0 rhs)
        let sndEq := Sierra.Expr.mkEq β y (Expr.proj `Prod 1 rhs)
        .cons fstEq [AndOrTree.separateTupleEqs (AndOrTree.cons sndEq ts)]
      | _, .some ⟨α, β, x, y⟩ =>
        let fstEq := Sierra.Expr.mkEq α (Expr.proj `Prod 0 lhs) x
        let sndEq := Sierra.Expr.mkEq β (Expr.proj `Prod 1 lhs) y
        .cons fstEq [AndOrTree.separateTupleEqs (AndOrTree.cons sndEq ts)]
      | _, _ => .cons e (AndOrTree.separateTupleEqs <$> ts)
    | .none => .cons e (AndOrTree.separateTupleEqs <$> ts)

/-- Contract equalities in an `AndOrTree` which fulfill a given criterion -/
partial def AndOrTree.contractEqs (t : AndOrTree) (crit : FVarId → Bool)
    (s : FVarSubst := .empty) (fvs : Std.HashSet FVarId := ∅) : AndOrTree :=
  match t with
  | nil => nil
  | cons e ts =>
    let e := s.apply e
    let (e, s) : Expr × FVarSubst := match e.eq? with
    | .some (_, lhs, rhs) =>
      if lhs == rhs then (q(True), s) else
      match lhs.fvarId?, rhs.fvarId? with
      | .some l, _ =>
        if crit l && ¬(fvs.contains l) then (q(True), s.insert l <| rhs)
        else (e, s)
      | _, some r =>
        if crit r && ¬(fvs.contains r) then (q(True), s.insert r <| lhs)
        else (e, s)
      | _, _ =>
        (e, s)
    | .none => (e, s)
    let fvs := fvs.insertMany e.getFVars
    cons e <| ts.map <| fun t => t.contractEqs crit s fvs

def OfInputs (R : Type) : List Q(Type) → Type
| []        => R
| (T :: Ts) => Q($T) → OfInputs R Ts

def OfInputs.const {R : Type} (r : R) : {Ts : List Q(Type)} → OfInputs R Ts
| []       => r
| (_ :: _) => fun _ => OfInputs.const r

instance [Inhabited R] : Inhabited (OfInputs R Ts) := ⟨OfInputs.const default⟩

/-- Lambda-close an `OfInputs` instance. -/
def OfInputs.toExpr {Ts : List Q(Type)} (f : OfInputs Q(Prop) Ts) : MetaM Expr :=
match Ts with
| [] => pure f
| (T :: Ts) =>
  withLocalDeclD (.mkSimple s!"x{Ts.length}") T fun fv => do
    let r ← OfInputs.toExpr (f fv)
    mkLambdaFVars #[fv] r

def OfInputs.apply {R : Type} [Inhabited R] {Ts : List Q(Type)} (f : OfInputs R Ts)
    (ts : List Expr) : R :=
  match Ts, ts with
  | [],       []        => f
  | (_ :: _), (t :: ts) => OfInputs.apply (f t) ts
  | _,        _         => panic "Wrong number of arguments supplied to OfInputs"

def OfInputs.abstract {R : Type} {Ts : List Q(Type)} (k : List Expr → R) (acc : List Expr := []) :
    OfInputs R Ts :=
  match Ts with
  | [] => k acc
  | _::_ => fun x => OfInputs.abstract k (acc.append [x])

def OfInputs.map {R R' : Type} {Ts : List Q(Type)} (f : R → R') : OfInputs R Ts → OfInputs R' Ts :=
match Ts with
| [] => f
| _::_ => fun r t => OfInputs.map f (r t)

def listToExpr : List Q(Type) → Q(List Type)
  | [] => q([])
  | a :: as => q($a :: $(listToExpr as))

def OfInputsQ (r : Q(Type)) : List Q(Type) → Q(Type)
| []        => r
| (t :: ts) => q($t → $(OfInputsQ r ts))

def quoteFin {n : Nat} (x : Fin n) : Q(Fin $n) :=
match n, x with
| .succ _, ⟨m, _⟩ => q(Fin.ofNat' _ $m)

instance {n : Nat} : ToExpr (Fin n) := { toExpr := quoteFin, toTypeExpr := q(Type) }
