import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "f3dd5c320d6039ddbc829e869d918f8c1fd24920"

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
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "9af4c720f08e9c694e574fc35cf59b385be47175"
