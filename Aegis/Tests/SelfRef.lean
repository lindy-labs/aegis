import Aegis.Commands
import Aegis.Macros

open Sierra Lean

aegis_load_file "issue2249.sierra"

aegis_spec "issue2249::issue2249::simple_test" :=
  fun _ ρ => ρ = .inl (12, .inr ())

aegis_prove "issue2249::issue2249::simple_test" :=
  fun _ ρ => by
  unfold «spec_issue2249::issue2249::simple_test»
  aesop

aegis_complete
