import Lean

open Lean Elab Parser.Tactic Parser.Tactic.Grind

namespace rGrind

/-- A *restricted* `grind` that always runs with ematching disabled:
`(ematch := 0)` is appended to the configuration, overriding any value the
caller passed.

It is `scoped`, so it only takes effect in files that `open rGrind`
(or `open scoped rGrind`). Because `open` is file-local and is *not*
re-exported, a file that merely imports such a file is **not** affected.

The parser captures *every* surface form of `grind` — bare `grind`,
with config (`grind (…)`, `grind +flag`), `grind only`, `grind [lemmas]`,
and `grind => …` — so none of them can escape the restriction. -/
scoped syntax (name := gGrind) (priority := high)
  "grind" optConfig (&" only")? (" [" grindParam,* "]")? (" => " grindSeq)? : tactic

/-- Expansion for the scoped restricted `grind`.

It appends `(ematch := 0)` to the `optConfig` (placed last, so it overrides any
`ematch` the caller set) and retags the node with the *core* `grind` kind. The
builtin `grind` elaborator then runs exactly once on the rewritten node — there
is no re-match against this macro, hence no infinite recursion. -/
@[macro gGrind] def expandRestrictedGrind : Macro := fun stx => do
  let ematch0 ← `(configItem| (ematch := 0))
  -- `optConfig` is `(configItem)*`, i.e. a single null node holding the items.
  let optCfg := stx[1]
  let items  := optCfg[0]
  let optCfg := optCfg.setArg 0 (items.setArgs (items.getArgs.push ematch0.raw))
  return (stx.setArg 1 optCfg).setKind ``Lean.Parser.Tactic.grind

end rGrind
