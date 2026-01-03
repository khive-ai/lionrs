import Lake
open Lake DSL

package «lionrs» where
  version := v!"2.0.0"
  preferReleaseBuild := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.23.0"

-- Lion microkernel formal proofs
@[default_target]
lean_lib «Lion» where
  roots := #[`Lion]
  globs := #[.submodules `Lion]
