# German language style

* Anreden klein (du, ihr, euch)
* Format für direkte Rede:
  ```
  **Robo**:
  **Robo** *(flüsternd)*:
  ```
* Okay (nicht Okay, nicht OK, nicht Oke, nicht O.K. …)
* Doppel-S (ß) nach Deutscher Grammatik, nicht Schweizer🥲.

# Strategic decisions regarding Tactics

* In general, we want to *advertise* automation, not hide it.  Therefore:
  - `tauto` is allowed (except on the first few planets, were we want to introduce a few other basic tactics in an elementary setting)
  - We introduce `decide`.
  - We won't employ `linear_combination`.  We would rather want to use `polyrith`, but that would require some engineering and might create security issues.
* We don't use `rcases` but rather `obtain`.
  - `obtain` is more pronouncable and more of a word.
  - `obtain` seems to be encouraged over `rcases` in mathlib.
* We use `choose` instead of `obtain` for all existential hypotheses.
* We encourage students to distinguish the tacticts `rfl`, `assumption`, `contradiction` and `decide`.
  We do not introduce `trivial` (even though `trivial` can do all of the above).
* Generally speaking, we try not to introduce too many tactics (but see previous point for an important exception).
  - We use `let` but not `set` tactic.
    - We don't currently need `set`.
    - `set` does not operate on sets the way `ring` operates on rings, which might be confusing and don't need it.
    - We believe `let` is more common in mathlib than `set`.
  - For functions, we use `funext` tactic, `apply congr_arg` and `apply congr_fun`.
    We might have used the `congr` tactic instead of `congr_arg` and `congr_fun`, but `congr` does not appear to be able to reduce `f a = g a` to `f = g` (for functions `f` and `g`).

# Inventory Doc

The point of all documentation is make the explanations that Robo provides available for later reference.  It may be copied over verbatim from the corresponding levels.

- Tactics should always have a (short) documentation.  We bundle these in `Game/Doc/Tactic.lean`.
- Definitions should have a documentation that describes the most common strategy for dealing with them.
  We bundle these in `Game/Doc/Definition.lean`.
- Theorems are documented only in exceptional cases.
  They are documented in the level file in which they are introduced.
