import Lean

open Lean Elab Parser.Tactic Parser.Tactic.Grind

/-! # Restricted `grind` by default

Importing this module makes `grind` **restricted everywhere** (it always runs
with `(ematch := 0)`). Every surface form is covered — bare `grind`, config
(`grind (…)`, `grind +flag`, `grind -flag`), `grind only`, `grind [lemmas]`,
and `grind => …`.

To get the full, unrestricted `grind` in a particular file, write

```lean
open FullGrind
```

at the top of that file (or `open AllowFullGrind in` before a single command).
Because `open` is file-local and is *not* re-exported, the opt-out does not leak
to files that import yours. -/

namespace RestrictedGrind

/-- Global, high-priority parser capturing *every* surface form of `grind`.
It is **not** `scoped`, so it is active in every file that (transitively)
imports this module — making restricted `grind` the default. -/
syntax (name := gGrind) (priority := high)
  "grind" optConfig (&" only")? (" [" grindParam,* "]")? (" => " grindSeq)? : tactic

/-- Append `(ematch := 0)` to the config (last, so it overrides any caller value)
and retag the node with the core `grind` kind, so the builtin elaborator runs
exactly once — no re-match, no recursion. -/
@[macro gGrind] def expandRestrictedGrind : Macro := fun stx => do
  let ematch0 ← `(configItem| (ematch := 0))
  let optCfg := stx[1]
  let items  := optCfg[0]
  let optCfg := optCfg.setArg 0 (items.setArgs (items.getArgs.push ematch0.raw))
  return (stx.setArg 1 optCfg).setKind ``Lean.Parser.Tactic.grind

end RestrictedGrind

namespace FullGrind

/-- Even-higher-priority parser for `grind`, but `scoped`: it is only active in
files that `open AllowFullGrind`. When active it outranks the restricted parser
and restores the unrestricted `grind`. -/
scoped syntax (name := gFullGrind) (priority := high + 1)
  "grind" optConfig (&" only")? (" [" grindParam,* "]")? (" => " grindSeq)? : tactic

/-- Passthrough: retag as core `grind` with no config injected (full power). -/
@[macro gFullGrind] def expandFullGrind : Macro := fun stx =>
  return stx.setKind ``Lean.Parser.Tactic.grind

end FullGrind
