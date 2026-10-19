import Lake
open Lake DSL

package max_caterpillar where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.4.0"

lean_lib MaxNN where
lean_lib MaxCaterpillar where
lean_lib Verification where

@[default_target]
lean_lib All where
