import Aegis.Tactic

namespace Sierra.Test.Array.ArrayPopFrontConsume

aegis_load_file "../../e2e_libfuncs/array_aegis/array_pop_front_consume.sierra"

aegis_spec "test::foo" :=
  fun m a ρ =>
  (∃ hd tl ρ', a = hd::tl ∧ ρ = .inl (tl, ρ') ∧ m.boxHeap .Felt252 ρ' = .some hd)
  ∨ a = [] ∧ ρ = .inr ()

aegis_prove "test::foo" :=
  fun m a ρ => by
  unfold_spec "test::foo"
  aesop
