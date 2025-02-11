import Aegis.Tactic

namespace Sierra.Test.Array.ArraySnapshotPopBack

aegis_load_file "../../e2e_libfuncs/array_aegis/array_snapshot_pop_back.sierra"

aegis_spec "test::foo" :=
  fun m a ρ₁ ρ₂ =>
  ρ₁ = a.take (a.length - 1)
  ∧ (a.length = 0 ∧ ρ₂ = .inr ()
    ∨ ∃ ρ₂', ρ₂ = .inl ρ₂' ∧ m.boxHeap .Felt252 ρ₂' = .some a.getLast!)

aegis_prove "test::foo" :=
  fun m a ρ₁ ρ₂ => by
  unfold_spec "test::foo"
  have : ∀ (xs : List F) x, (xs ++ [x]).getLast! = x := by
    intro xs x
    induction' xs
    · simp [List.getLast!]
    · simp [List.getLast!]
  aesop

aegis_complete
