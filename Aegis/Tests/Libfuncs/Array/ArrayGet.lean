import Aegis.Tactic

namespace Sierra.Test.Array.ArrayGet

aegis_load_file "../../e2e_libfuncs/array_aegis/array_get.sierra"

aegis_spec "test::foo" :=
  fun m _ a i _ ρ =>
  (∃ ref4,
    BitVec.toNat i < a.length ∧
        (∃ ρ', m.boxHeap SierraType.Felt252.Array ref4 = some ρ' ∧ a[BitVec.toNat i]? = some ρ') ∧ Sum.inl ref4 = ρ ∨
      a.length ≤ BitVec.toNat i ∧ Sum.inr () = ρ)

aegis_prove "test::foo" :=
  fun m _ a i _ ρ => by
  unfold_spec "test::foo"
  intro h
  exact h

aegis_complete
