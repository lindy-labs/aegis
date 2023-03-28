import Lake
open Lake DSL

package «sierra-lean» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "1b816f73febb09913b30c973d6fa08f5c6462eb0"

require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean" @ "7331b206ce132746ff7653ac63d1ff9491c8f8c9"

lean_lib SierraLean {
  -- add library configuration options here
}

@[default_target]
lean_exe «sierra-lean» {
  root := `Main
}
