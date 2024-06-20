import Mathlib.Data.ZMod.Basic

namespace ZMod

variable {n : ℕ} (a b : ZMod n)

example : Div ℤ := inferInstance

/-- Division of number in `ZMod n` as if they were natural numbers. -/
def ndiv : ZMod n :=
  match n with
  | 0       => a.val / b.val
  | .succ _ => ⟨a.val / b.val, lt_of_le_of_lt (Nat.div_le_self _ _) a.val_lt⟩

@[simp]
theorem val_ndiv : (ndiv a b).val = a.val / b.val := by cases n <;> rfl

/-- Mod of numbers in `ZMod n` as if they were natural numbers. -/
def nmod : ZMod n := a.val % b.val

@[simp]
theorem val_nmod (hb : b ≠ 0) : (nmod a b).val = a.val % b.val := by
  simp only [nmod]
  cases n
  · simp_all only [Nat.zero_eq, ne_eq]
    rfl
  · have : 0 < b.val := by
      rw [Nat.pos_iff_ne_zero]
      intro h
      rw [val_eq_zero] at h
      contradiction
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ this) b.val_lt)]
