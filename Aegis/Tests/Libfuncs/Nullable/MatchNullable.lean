import Aegis.Tactic

namespace Sierra.Test.Nullable.MatchNullable

aegis_load_file "../../e2e_libfuncs/nullable_aegis/match_nullable.sierra"

aegis_spec "test::foo" :=
  fun m a b ρ =>
  a.elim (ρ = b) (fun x => m.boxHeap .Felt252 ρ = .some x)

aegis_prove "test::foo" :=
  fun m a b ρ => by
  unfold_spec "test::foo"
  intro h_auto
  simp_all only [Option.elim]
  aesop

aegis_complete
