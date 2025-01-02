import Aegis.Tactic

namespace Sierra.Test.Box.Unbox

aegis_load_file "../../e2e_libfuncs/box_aegis/unbox.sierra"

aegis_spec "test::foo" :=
  fun m a _ =>
  m.boxHeap (.Struct []) a = .some ()

aegis_prove "test::foo" :=
  fun m a _ => by
  unfold_spec "test::foo"
  rintro ⟨_,h,-⟩
  exact h.symm
