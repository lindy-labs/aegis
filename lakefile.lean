import Lake
open Lake DSL

package «aegis» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.10.0-rc2"

@[default_target]
lean_lib Aegis {
  -- add library configuration options here
}
