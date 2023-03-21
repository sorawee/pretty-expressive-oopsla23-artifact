import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "7ca25b3affcf79c45bc1f3159aa840b4ecb6ad02"

package «pretty» {
  -- add package configuration options here
}

@[default_target]
lean_lib «Pretty» {
  -- Compile everything under Pretty
  globs := #[`Pretty, .submodules `Pretty]
  -- Treat warnings (e.g. presence of sorry) as errors
  moreLeanArgs := #[
    "-DwarningAsError=true"
  ]
}

-- Enable doc-gen4
meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "b9421b9a12b148d9279a881cce227affdb09ed08"
