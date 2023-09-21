import Lake
open Lake DSL

package «aegis» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "d383329f78ac8ede32891dece0f8ce7caf9ef767"

@[default_target]
lean_lib Aegis {
  -- add library configuration options here
}

