import Aegis.Commands

open Sierra

aegis_load_file "../../e2e_libfuncs/array_aegis/array_slice.sierra"

aegis_spec "test::foo" :=
  fun _ _ a i j _ ρ =>
  i.val ≤ j.val ∧ j.val ≤ a.length ∧ ρ = .inl a.toArray[i.val:j.val].toArray.toList
  ∨ (j.val < i.val ∨ a.length < j.val) ∧ ρ = .inr ()

aegis_prove "test::foo" :=
  fun _ _ a i j _ ρ => by
  unfold «spec_test::foo»
  rename_i x x_1 x_2
  intro h_auto
  simp_all only [Array.toList_eq]
  unhygienic aesop_cases h_auto
  · simp_all only [and_self, true_or]
  · simp_all only [and_self, or_true]
