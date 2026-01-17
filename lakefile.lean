import Lake
open Lake DSL

package molecule where
  @[default_target]
  lean_lib Molecule

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

require mlc from git
  "https://github.com/kirill-kondrashov/yoccoz-theorem" @ "main"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

lean_exe check_axioms where
  root := `check_axioms
