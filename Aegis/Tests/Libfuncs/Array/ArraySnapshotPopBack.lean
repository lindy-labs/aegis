import Aegis.Commands

open Sierra

aegis_load_file "../../e2e_libfuncs/array_aegis/array_snapshot_pop_back.sierra"

aegis_spec "test::foo" :=
  fun m a ρ₁ ρ₂ =>
  ρ₁ = a.take (a.length - 1)
  ∧ (a.length = 0 ∧ ρ₂ = .inr ()
    ∨ ∃ ρ₂', ρ₂ = .inl ρ₂' ∧ m.boxHeap .Felt252 ρ₂' = .some a.getLast!)

aegis_prove "test::foo" :=
  fun m a ρ₁ ρ₂ => by
  unfold «spec_test::foo»
  have : ∀ (xs : List F) x, (xs ++ [x]).getLast! = x := by
    intro xs x
    induction' xs
    · simp [List.getLast!]
    · simp [List.getLast!]
  intro h_auto
  unhygienic with_reducible aesop_destruct_products
  unhygienic aesop_cases h_1
  · unhygienic with_reducible aesop_destruct_products
    aesop_subst [right, right_1, left]
    simp_all only [List.length_append, List.length_singleton, add_tsub_cancel_right, List.take_left, add_eq_zero,
      one_ne_zero, and_false, and_self, Sum.inl.injEq, exists_eq_left', or_true]
  · simp_all only [and_true]
    unhygienic with_reducible aesop_destruct_products
    aesop_subst [left, right_1, left_1]
    simp_all only [List.length_nil, ge_iff_le, zero_le, tsub_eq_zero_of_le, List.take_nil, false_and, exists_const,
      or_false, and_self]

aegis_complete
