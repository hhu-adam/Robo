import Game.Metadata

World "Smooth"
Level 1

open Polynomial

Introduction "Intro Smooth L01"

/- Evaluating the polynomial `X ^ 2 + 1` at `2` gives `5`. -/
Statement : (X ^ 2 + 1 : ℝ[X]).eval 2 = 5 := by
  Hint "A polynomial is a *formal* expression built from the variable `X : ℝ[X]` and constants.
  It is not yet a function. To get values you *evaluate* it,
  and `p.eval a` substitutes `a` for `X`."
  Hint (hidden := true) "[Hint tkwd] `simp` knows how evaluation interacts with `+`, `^`, `X`
  and constants."
  simp
  Hint (hidden := true) "[Hint smth1tr] Try `ring`."
  ring

NewDefinition Polynomial Polynomial.X Polynomial.eval
