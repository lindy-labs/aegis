import Aegis.Commands

open Sierra

aegis_load_file "../../e2e_libfuncs/array_aegis/array_get.sierra"

aegis_spec "test::foo" :=
  fun m _ a i _ ρ =>
  i.val < a.length
    ∧ (∃ ρ' b, ρ = .inl ρ' ∧ a.get? i.val = .some b
      ∧ m.boxHeap (SierraType.Array SierraType.Felt252) ρ' = .some b)
  ∨ a.length ≤ i.val ∧ ρ = .inr ()

aegis_prove "test::foo" :=
  fun m _ a b _ ρ => by
  unfold «spec_test::foo»
  rintro ⟨x,(h|h)⟩
  · rename_i x_1 x_2
    simp_all only [exists_and_left, true_and]
    unhygienic with_reducible aesop_destruct_products
    aesop_subst right_1
    simp_all only [Sum.inl.injEq, Option.some.injEq, exists_eq_left', and_false, or_false]
  · simp [h]

aegis_complete
