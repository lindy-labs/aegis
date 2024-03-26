import Aegis.Commands

open Sierra

aegis_load_file "../../e2e_libfuncs/nullable_aegis/match_nullable.sierra"

aegis_spec "test::foo" :=
  fun m a b ρ =>
  a.elim (ρ = b) (fun x => m.boxHeap .Felt252 ρ = .some x)

aegis_prove "test::foo" :=
  fun m a b ρ => by
  unfold «spec_test::foo»
  intro h_auto
  simp_all only [Option.elim]
  unhygienic with_reducible aesop_destruct_products
  unhygienic aesop_cases h
  · simp_all only
  · simp_all only
    unhygienic with_reducible aesop_destruct_products
    aesop_subst [left_1, right_1]
    split
    · simp_all only [Option.isSome_some]
    · simp_all only [Option.isSome_none]

aegis_complete
