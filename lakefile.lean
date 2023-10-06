import Lake
open Lake DSL

package «aegis» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "167880ba45c8aa187d774c5b59f6b9a80ff9b935"

@[default_target]
lean_lib Aegis {
  -- add library configuration options here
}

