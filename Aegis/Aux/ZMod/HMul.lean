import Mathlib.Data.ZMod.Basic


namespace ZMod

variable {n : ℕ} (a b : ZMod n)

def hmul : ZMod n :=
  match n with
  | 0 => 0
  | .succ n => ⟨a.val * b.val / (n + 1), by
      apply lt_of_le_of_lt (Nat.div_le_div_right (Nat.mul_le_mul_right _ (le_of_lt a.val_lt))) _
      rw [Nat.mul_div_right _ (Nat.succ_pos _)]
      exact b.val_lt⟩
