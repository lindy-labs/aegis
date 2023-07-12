import SierraLean.Aux.ZMod.DivMod
import SierraLean.Aux.Bool

namespace Sierra

syntax "sierra_simp" : tactic

macro_rules
| `(tactic|sierra_simp) => 
  `(tactic| 
    simp only [Prod.mk.inj_iff, and_assoc, Bool.coe_toSierraBool, Bool.toSierraBool_coe,
      exists_and_left, exists_and_right, exists_eq_left, exists_eq_right, exists_eq_right',
      exists_eq_left', SierraBool_toBool_inl, SierraBool_toBool_inr, not, or, Bool.toSierraBool_true,
      Int.ofNat_eq_coe, Nat.cast_one, Nat.cast_zero, Int.cast_zero, ZMod.val_zero,
      exists_or, exists_const, ← or_and_right];
    simp only [← exists_and_left, ← exists_and_right, ← exists_or])
