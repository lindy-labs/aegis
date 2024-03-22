import Aegis.Commands

open Sierra

aegis_load_file "../../e2e_libfuncs/array_aegis/array_pop_front_consume.sierra"

aegis_spec "test::foo" :=
  fun m a ρ =>
  (∃ hd tl ρ', a = hd::tl ∧ ρ = .inl (tl, ρ') ∧ m.boxHeap .Felt252 ρ' = .some hd)
  ∨ a = [] ∧ ρ = .inr ()

aegis_prove "test::foo" :=
  fun m a ρ => by
  unfold «spec_test::foo»
  intro h_auto
  simp_all only [exists_eq_right_right', exists_and_left]
  unhygienic with_reducible aesop_destruct_products
  unhygienic aesop_cases h_1
  · unhygienic with_reducible aesop_destruct_products
    aesop_subst [right, left]
    simp_all only [List.cons.injEq, Sum.inl.injEq, Prod.mk.injEq, and_self, or_false]
    apply Exists.intro
    apply Exists.intro
    apply And.intro
    apply And.intro
    on_goal 2 => apply Eq.refl
    on_goal 2 => simp_all only [true_and, exists_eq_left', Option.some.injEq]
    on_goal 2 => apply Eq.refl
    simp_all only
  · simp_all only [false_and, exists_const, and_self, or_true]
