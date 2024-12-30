import Aegis.Tactic

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
  unfold_spec "test::foo"
  rintro ⟨x,(h|h)⟩
  · aesop
  · simp [h]

aegis_complete
