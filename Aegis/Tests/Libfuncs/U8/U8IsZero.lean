import Aegis.Tactic

namespace Sierra.Test.U8.U8IsZero

aegis_load_file "../../e2e_libfuncs/u8_aegis/u8_is_zero.sierra"

aegis_spec "test::foo" :=
  fun _ a ρ =>
  ρ =  if a = 0 then 123 else a

aegis_prove "test::foo" :=
  fun _ a ρ => by
  unfold_spec "test::foo"
  rintro (⟨rfl,rfl⟩|⟨h,rfl⟩)
  · rfl
  · aesop

aegis_complete
