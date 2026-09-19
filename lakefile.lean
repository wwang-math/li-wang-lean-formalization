import Lake
open Lake DSL

package «LiWangLeanFormalization» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require "leanprover-community" / "mathlib" @ git "8d6f23e07b24c7dda53bb66ba1acaf7b99c9adf6"

@[default_target]
lean_lib «LiWangWiener» where
  globs := #[.andSubmodules `LiWangWiener]
