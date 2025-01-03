import Aegis.Tactic

namespace Sierra.Test.Array.ArraySlice

aegis_load_file "../../e2e_libfuncs/array_aegis/array_slice.sierra"

aegis_spec "test::foo" :=
  fun _ _ a i j _ ρ =>
  i.toNat ≤ j.toNat ∧ j.toNat ≤ a.length ∧ ρ = .inl a.toArray[i.toNat:j.toNat].toArray.toList
  ∨ (j.toNat < i.toNat ∨ a.length < j.toNat) ∧ ρ = .inr ()

aegis_prove "test::foo" :=
  fun _ _ a i j _ ρ => by
  unfold_spec "test::foo"
  rename_i x x_1 x_2
  intro h_auto
  cases h_auto
  · simp_all only [and_self, true_or]
  · simp_all only [and_self, or_true]
