import Lake
open Lake DSL

def LocalGameServer : Dependency := {
  name := `GameServer
  src := Source.path "../lean4game/server"
}

def RemoteGameServer : Dependency := {
  name := `GameServer
  src := Source.git "https://github.com/leanprover-community/lean4game.git" "73b80e714dd4712f11675a59d67980e3815b53c9" "server"
}

/- Choose dependency depending on the environment variable NODE_ENV -/
open Lean in
#eval (do
  let gameServerName :=
    if (← IO.getEnv "NODE_ENV") == some "development" then ``LocalGameServer else ``RemoteGameServer
  modifyEnv (fun env => Lake.packageDepAttr.ext.addEntry env gameServerName)
   : Elab.Command.CommandElabM Unit)

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "658235826386f03bfb2b231fa42ead956567ce60"

package Game where
  moreLeanArgs := #["-Dtactic.hygienic=false"]
  moreServerArgs := #["-Dtactic.hygienic=false"]

@[default_target]
lean_lib Game
