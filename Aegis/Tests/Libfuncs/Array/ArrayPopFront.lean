import Aegis.Tactic

namespace Sierra.Test.Array.ArrayPopFront

aegis_load_file "../../e2e_libfuncs/array_aegis/array_pop_front.sierra"

aegis_spec "test::foo" :=
  fun m a ρ₁ ρ₂ =>
  ρ₁ = a.tail
  ∧ (a.length = 0 ∧ ρ₂ = .inr ()
    ∨ ∃ ρ₂', ρ₂ = .inl ρ₂' ∧ m.boxHeap .Felt252 ρ₂' = .some a.head!)

aegis_prove "test::foo" :=
  fun m a ρ₁ ρ₂ => by
  unfold_spec "test::foo"
  rintro ⟨_,_,(⟨⟨ρ₂',h,rfl⟩,rfl,rfl⟩|⟨rfl,rfl,rfl⟩)⟩
  · rename_i w w_1
    simp_all only [List.tail_cons, List.length_cons, Nat.succ_ne_zero, and_self, Sum.inl.injEq, List.head!_cons,
      exists_eq_left', or_true]
  · simp

aegis_complete
