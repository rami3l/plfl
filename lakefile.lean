import Lake
open Lake DSL

package plfl {
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib Plfl {
  -- add library configuration options here
}

-- @[default_target]
-- lean_exe plfl {
--   root := `Main
-- }
