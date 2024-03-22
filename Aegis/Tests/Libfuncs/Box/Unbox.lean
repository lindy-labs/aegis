import Aegis.Commands

open Sierra

aegis_load_file "../../e2e_libfuncs/box_aegis/unbox.sierra"

aegis_spec "test::foo" :=
  fun m a _ =>
  m.boxHeap (.Struct []) a = .some ()

aegis_prove "test::foo" :=
  fun m a _ => by
  unfold «spec_test::foo»
  rintro ⟨_,h,-⟩
  exact h.symm
