import Lake
open Lake DSL

package «aegis» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "42649c4da2724d1aa86b8dab06079db71daf1a84"

@[default_target]
lean_lib Aegis {
  -- add library configuration options here
}
