import Aegis.Tactic

namespace Sierra.Test.U128.U128TryFromFelt252

aegis_load_file "../../e2e_libfuncs/u128_aegis/u128s_from_felt252.sierra"

aegis_spec "test::foo" :=
  fun _ _ a _ ρ =>
  a.val < U128_MOD ∧ ρ = .inl a.val
  ∨ U128_MOD ≤ a.val ∧ ρ.isRight ∧ ρ.getRight?.get!.1.append ρ.getRight?.get!.2 = a.val

aegis_prove "test::foo" :=
  fun _ _ a _ ρ => by
  unfold_spec "test::foo"
  aesop

aegis_complete
