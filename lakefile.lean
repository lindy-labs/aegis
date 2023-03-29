import Lake
open Lake DSL

package «sierra-lean» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "1b816f73febb09913b30c973d6fa08f5c6462eb0"

require YatimaStdLib from git
  "https://github.com/lurk-lab/YatimaStdLib.lean" @ "f39dca7a0815ee65e71776d46337f0240037ff6d"

require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean" @ "93b28d0ee4be435b6b395d8b6f816fabfc085166"

lean_lib SierraLean {
  -- add library configuration options here
}

@[default_target]
lean_exe «sierra-lean» {
  root := `Main
}
