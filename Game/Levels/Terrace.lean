import Game.Levels.Terrace.L01
import Game.Levels.Terrace.L02
import Game.Levels.Terrace.L03
import Game.Levels.Terrace.L04

/-!
The planet `Terrace` continues `Step`. It develops the `Finset` tools for peeling a finite
index set apart starting from its smallest element — `Finset.induction_on_min`, `Finset.min'`
with `Finset.min'_mem` and `Finset.min'_le` — and applies them in the boss level to show that
the uncountable family of step functions `step a`, `a : ℝ`, is linearly independent.
-/

World "Terrace"
Title "Terrace"

Introduction "Intro Terrace: peeling a finite set from its smallest element, and the
linearly independent family of step functions."
