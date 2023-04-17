import Lean.Meta.AppBuilder
import Qq

open Lean Qq

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

/-- A tree to contain expressions to be composed with `And` and `Or`.
If we want to avoid trees, this has to be replaced by some graph structure in the future. -/
inductive AndOrTree 
| nil  : AndOrTree
| cons : Expr → List AndOrTree → AndOrTree
deriving Inhabited, Repr

instance : ToString AndOrTree where toString x := toString $ repr x

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

def OfInputs (R : Type) : List Q(Type) → Type
| []        => R
| (T :: Ts) => Q($T) → OfInputs R Ts

def OfInputs.const {R : Type} (r : R) : {Ts : List Q(Type)} → OfInputs R Ts
| []       => r
| (_ :: _) => fun _ => OfInputs.const r

def OfInputs.apply {R : Type} [Inhabited R] {Ts : List Q(Type)} (f : OfInputs R Ts) 
    (ts : List Expr) : R :=
  match Ts, ts with
  | [],       []        => f
  | (_ :: _), (t :: ts) => OfInputs.apply (f t) ts
  | _,        _         => panic "Wrong number of arguments supplied to OfInputs"

def listToExpr : List Q(Type) → Q(List Type)
  | [] => q([])
  | a :: as => q($a :: $(listToExpr as))
