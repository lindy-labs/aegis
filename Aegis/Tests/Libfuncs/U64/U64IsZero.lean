import Aegis.Tactic

namespace Sierra.Test.U64.U64IsZero

aegis_load_file "../../e2e_libfuncs/u64_aegis/u64_is_zero.sierra"

aegis_spec "test::foo" :=
  fun _ a ρ =>
  ρ =  if a = 0 then 1234 else a

aegis_prove "test::foo" :=
  fun _ a ρ => by
  unfold_spec "test::foo"
  rintro (⟨rfl,rfl⟩|⟨h,rfl⟩)
  · rfl
  · aesop

aegis_complete
