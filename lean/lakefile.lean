import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "a14fcecbe1b1a1d6c9d11878606b3a7a54e9cb97"

package «pretty» {
  -- add package configuration options here
}

@[default_target]
lean_lib «Pretty» {
  -- Compile Pretty.lean, which should import every submodules under Pretty/
  -- Run `racket scripts/gen-main.rkt` to generate Pretty.lean
  globs := #[`Pretty]
  -- Treat warnings (e.g. presence of sorry) as errors
  moreLeanArgs := #[
    "-DwarningAsError=true"
  ]
}

-- Enable doc-gen4
meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "8ea6a55a82ecb27f1c5290c5249d8490af855d3a"
