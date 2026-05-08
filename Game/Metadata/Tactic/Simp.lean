import Lean.Meta.Tactic.Simp
import Game.Metadata.Tactic.SimpLog

/** Custom simp set to restrict the player's simp calls. */
register_simp_attr game_simp

/- `simp` tatics for player -/
macro_rules
  | `(tactic| simp)                          => `(tactic| try simp only [game_simp])
  | `(tactic| simp [$args,*])                => `(tactic| try simp only [game_simp, $args,*])
  | `(tactic| simp $loc:location)            => `(tactic| try simp only [game_simp] $loc:location)
  | `(tactic| simp [$args,*] $loc:location)  => `(tactic| try simp only [game_simp, $args,*] $loc:location)

/- `simp?` versions -- not currently enabled in game -/
macro_rules
  | `(tactic| simp?)                         => `(tactic| try simp? only [game_simp])
  | `(tactic| simp? [$args,*])               => `(tactic| try simp? only [game_simp, $args,*])
  | `(tactic| simp? $loc:location)           => `(tactic| try simp? only [game_simp] $loc:location)
  | `(tactic| simp? [$args,*] $loc:location) => `(tactic| try simp? only [game_simp, $args,*] $loc:location)

/- For authoring: write `simp_log` (defined in `Game.Metadata.Tactic.SimpLog`)
   instead of `simp` while developing a level. It runs the full simp set and
   logs every used lemma's fully qualified name during `lake build`, so
   `extract_simp_lemmas.py` can collect them into `simp_list.lean`. -/


/-
# Notes on possible further enhancements

# Question
I would like to make a restricted version of "simp" available in the game.  This version should not
use all simp lemmas available in the context, but only a subset "game_simp" of game specific simp
  lemmas authorized by the author of the game.  I have not yet decided on the following points:

  - static versus dynamic set of simp lemmas:  Should game_simp be a static list, or should it also
    evolve dynamically like the list of available theorems we discussed above, with more simp lemmas
    being
    unlocked as the game progresses?
  - manual versus automated generation of game_simp list:  Ideally, there would be some tatic
    author_simp that the author of a game can use in proofs, and this tactic would automatically add
    all lemmas
    used by simp to the list game_simp.  Alternatively, there could be a command "NewSimpTheorem"
    similar to "NewTheorem" with which the author manually lists all simp lemmas used in the proof.
  - hidden versus visible simp lemmas:  should the lemmas from the list game_simp be displayed as
    part of the inventory or not?

  I suppose static/manual/hidden would be much easier to implement.  I started some work in this
  direction in Robo/Game/Metadata/test/simp.lean, and I would be quite happy to get this kind of
  basic implication up and running for now.  But on the other hand, this does not seem to tie in with the
  existing logic for inventory management at all, and perhaps, in the long run, treating simp lemmas
  differently from "normal" lemmas will increase the overall complexity of the game logic rather
  than keeping things simple.  So, for each question above, could you please assess whether my
  wishes seem feasible at all; if so, which option would be easier to implement; and finally how much more
  difficult the other option would be?



# Answer (Claude Opus, medium effort)

**summary:**
- stick with static  + manual + hidden   for now
- aim for    dynamic + manual + visible  in long term
  (don't try automatic


### Q1: Static vs. dynamic

**Both feasible. Static is essentially free (you have it). Dynamic is medium work.**

Static works because the `@[game_simp]` attribute is just a global Lean simp set — the macro
indirection is per-game, not per-level.

Dynamic is harder because `macro_rules` is a purely syntactic rewrite — it has no access to "what
level is this?". To make `simp` use a *different* subset per level, you'd need to abandon the macro
approach for a real elaborator: a custom `game_simp` tactic that, at elaboration time, reads the
unlocked-simp-lemmas list for the current level and builds a `Simp.Context` from it. This ties
cleanly into the existing framework — you'd add a `simpLemmas : InventoryInfo` field to `GameLevel`,
a `NewSimpTheorem` command parallel to `NewTheorem`, and `MakeGame` would compute `simpLemmas.tiles`
exactly as it already does for `lemmas`. The `Runner` is already set up to inject level info, so the
custom tactic can read it.

So: static = done; dynamic ≈ 1–2 days of work, but it slots into the existing per-level inventory
machinery rather than fighting it.

**My take:** if you suspect you'll want simp lemmas to unlock progressively (e.g. early levels: only
commutativity rules; later: distributivity etc.), the dynamic option is worth the investment — and
it's not much more complex *because* the framework already does this for theorems. If the set is
small enough that "always available" is fine, static is great.

---

### Q2: Manual (`NewSimpTheorem`) vs. automated extraction from `author_simp`

**Manual is trivially easy. Automated is medium-high difficulty, and I'd argue it's the *wrong*
default.**

Manual is ~15 lines: clone `NewTheorem` from `Commands.lean:271`, point it at a new `simpLemmas`
field, register a `simp_attr` extension. You already have the attribute side working.

Automated extraction is feasible. `simp` and `simp?` already track usage internally via
`Lean.Meta.Simp.UsedSimps`; `simp?` exposes it via `traceSimpCall`. So `author_simp` could run
`simp`, capture `UsedSimps`, and side-effect those names into the current level's metadata. Maybe a
day's work once you've located the right hooks.

But — the design concern: real Mathlib `simp` calls pull in dozens of low-level simp lemmas
(decidability instances, `Nat.reducedAdd`-flavored normalizers, coercion lemmas) that you almost
certainly don't want surfaced to a beginner player. So automated extraction would need a curation
step anyway — at which point the author is doing manual work, just *editing a generated list*
instead of writing it. That's still a real ergonomic win, but not the order-of-magnitude one might
hope for.

**My take:** manual first. If it becomes painful in practice, add `author_simp?` (which you
essentially already have) and let the author copy-paste the suggested lemma list into a
`NewSimpTheorem` line. That gives you 80% of the automation benefit with 0% of the implementation
cost.

---

### Q3: Hidden vs. visible

**Hidden is what you have. Visible is the right long-term default, and only a little more work *if*
you go dynamic.**

Hidden's drawback is UX: when `simp` mysteriously fails on a goal a player thinks is "obvious," they
have no way to know what `simp` can actually do. With a curated set this is more confusing than with
full Mathlib `simp`.

Visible is essentially free *if* you've already added a `simpLemmas` field tracked per-level:
`MakeGame` computes tiles, `LevelInfo` exposes them, the frontend inventory panel renders them —
possibly as a new category, or as a "simp" badge on existing theorem tiles when a lemma is both. The
frontend changes are small.

If you stay static, "visible" still works — you'd just emit one global list at game-build time — but
the existing inventory UI is per-level, so you'd be wedging a global panel into a per-level UI.

**My take:** visibility pairs naturally with dynamic. Hidden pairs naturally with static. Mixing
(static + visible, or dynamic + hidden) creates friction in both directions.

---

### Recommendation

Two coherent points in the design space:

1. **MVP (what you have):** static + manual + hidden. Ship it. ~0 additional work.
2. **Long-term integration:** dynamic + manual + visible. Add a `NewSimpTheorem` command and a
   `simpLemmas : InventoryInfo` field; replace the `macro_rules` with a custom elaborator that reads
   the unlocked list; let `MakeGame` and the frontend handle display. Estimate 1–2 days.

I'd skip automated extraction unless authoring pain becomes real. The hybrid `author_simp?` → copy
suggestions into `NewSimpTheorem` workflow gets you most of the benefit for free.

The risk you flagged — "treating simp lemmas differently increases overall complexity" — is real for
the static/hidden path (it's a parallel system). It mostly *disappears* on the dynamic/visible path
because you're reusing the existing per-level inventory infrastructure rather than duplicating it.
So the long-term option is, paradoxically, the one that keeps the framework's conceptual surface
smaller.
-/
