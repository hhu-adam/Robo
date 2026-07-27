import Game.Metadata
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

World "Smooth"
Level 1

open Polynomial

Introduction "Intro Smooth L01:
Remember that you have already met multivariate polynomial in Saturn.
`Polynomial ℝ` is the type of polynomials with real coefficients; Mathlib
provides the usual notation `ℝ[X]` for it. A polynomial is a *formal*
expression built from the variable `X : ℝ[X]` and constants — for example
`X ^ 2 + 1`. It is not yet a function: to get values you *evaluate* it, and
`p.eval a` substitutes `a` for `X`.

As a first step, compute the value of `X ^ 2 + 1` at `2`.
"

/- Evaluating the polynomial `X ^ 2 + 1` at `2` gives `5`. -/
Statement : (X ^ 2 + 1 : ℝ[X]).eval 2 = 5 := by
  Hint "[Hint tkwd] `simp` knows how evaluation interacts with `+`, `^`, `X`
  and constants."
  simp
  Hint (hidden := true) "[Hint smth1tr] Try `ring`."
  ring

NewDefinition Polynomial Polynomial.X Polynomial.eval
