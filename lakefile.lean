import Lake
open Lake DSL

package «aegis» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "c853142823a3541b0e422362e263dc692c64298c"

@[default_target]
lean_lib Aegis {
  -- add library configuration options here
}

