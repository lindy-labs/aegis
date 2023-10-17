import Aegis.Commands
import Aegis.Macros

open Sierra Lean

aegis_load_file "Aegis/Tests/issue2249.sierra"

aegis_info "issue2249::issue2249::simple_test"

aegis_spec "issue2249::issue2249::simple_test" := 
  fun _ ρ => True

aegis_prove "issue2249::issue2249::simple_test" := 
  fun _ ρ => by
  sorry

aegis_complete

