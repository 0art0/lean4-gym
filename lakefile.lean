import Lake
open Lake DSL

package «lean-gym» {
  -- add package configuration options here
}

lean_lib LeanGym {
  -- add library configuration options here
}

@[default_target]
lean_exe «lean-gym» {
  root := `LeanGym
  supportInterpreter := true
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"