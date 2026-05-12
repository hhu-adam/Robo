import Lean
import Lean.Elab.Tactic.Simp

/-!
# `simp_log`

A drop-in replacement for `simp` that, in addition to running `simp` normally,
emits an `info` diagnostic for every simp lemma actually used — by its
**fully qualified `Name`**, regardless of which namespaces are open.

This bypasses the pretty-printer that `simp?` runs over its `Try this`
suggestion (which strips namespaces of any `open`ed module).

The output lines look like:

  info: Game/Levels/Foo/Bar.lean:NN:MM: [simp_log] Set.mem_setOf_eq
  info: Game/Levels/Foo/Bar.lean:NN:MM: [simp_log] Nat.add_zero

so `extract_simp_lemmas.py` can grep them out of `lake build`.
-/

namespace Game

open Lean Elab Tactic Meta Parser.Tactic

/-- Same surface syntax as `simp`. -/
syntax (name := simpLog) "simp_log"
  optConfig
  (discharger)?
  (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*) "]")?
  (location)? : tactic

/-- Collect every `Syntax.ident` node in a tree. Used to find the identifiers
    the author explicitly passed to `simp_log [..]`, so we can resolve them and
    suppress their entries from the log. -/
private partial def collectIdents : Syntax → Array Syntax → Array Syntax
  | s@(.ident ..), acc => acc.push s
  | .node _ _ args, acc => args.foldl (init := acc) fun a s => collectIdents s a
  | _, acc => acc

@[tactic simpLog] def evalSimpLog : Tactic := fun stx => do
  -- Reuse the real simp pipeline. `mkSimpContext` reads positional children
  -- of `stx`; our syntax above mirrors `simp`'s shape, so the indices line up.
  let { ctx, simprocs, dischargeWrapper, .. } ← withMainContext <|
    mkSimpContext stx (eraseLocal := false)
  let stats ← dischargeWrapper.with fun discharge? =>
    simpLocation ctx simprocs discharge? (expandOptLocation stx[5])
  -- Resolve every author-supplied ident to its set of fully-qualified candidates
  -- (`realizeGlobalConstWithInfos` returns *all* matches, so it doesn't throw on
  -- overloaded names like `ne_comm`). Locals/unresolvable idents fall through
  -- harmlessly: they appear on the used side as `Origin.fvar`/`stx`, which we
  -- already skip below.
  let mut userNames : NameSet := {}
  for ident in collectIdents stx[4] #[] do
    try
      for n in (← Lean.Elab.realizeGlobalConstWithInfos ident) do
        userNames := userNames.insert n
    catch _ => pure ()
  for origin in stats.usedTheorems.toArray do
    match origin with
    | .decl declName _ _ =>
        unless userNames.contains declName do
          logInfoAt stx s!"[simp_log] {declName}"
    | _ => pure ()  -- skip fvar/stx/other; not useful as `attribute [game_simp]`

end Game
