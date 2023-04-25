import Lake
open Lake DSL

require GameServer from  git
  "https://github.com/leanprover-community/lean4game.git"@"main"/"server"/"leanserver"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"

package Adam where
  moreLeanArgs := #["-DautoImplicit=false", "-Dtactic.hygienic=false"]
  moreServerArgs := #["-DautoImplicit=false", "-Dtactic.hygienic=false"]

@[default_target]
lean_lib Adam
