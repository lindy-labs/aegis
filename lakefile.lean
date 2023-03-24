import Lake
open Lake DSL

package «sierra-lean» {
  -- add package configuration options here
}


require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean" @ "8859f129d199d5be82962140e9b886c0fd49e89c"


lean_lib SierraLean {
  -- add library configuration options here
}

@[default_target]
lean_exe «sierra-lean» {
  root := `Main
}
