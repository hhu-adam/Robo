import Game.Metadata
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

World "Smooth"
Level 1

open Polynomial

Introduction "
`Polynomial ℝ` is the type of polynomials with real coefficients; Mathlib
provides the usual notation `ℝ[X]` for it. A polynomial is a *formal*
expression built from the variable `X : ℝ[X]` and constants — for example
`X ^ 2 + 1`. It is not yet a function: to get values you *evaluate* it, and
`p.eval a` substitutes `a` for `X`.

As a first step, compute the value of `X ^ 2 + 1` at `2`.
"

/-- `Polynomial R` — with notation `R[X]` — is the type of polynomials with
coefficients in `R`. Its elements are formal expressions in the variable
`X`, such as `X ^ 2 + 1`. -/
DefinitionDoc Polynomial as "Polynomial"

/-- `X : R[X]` is the polynomial variable (the identity polynomial). -/
DefinitionDoc Polynomial.X as "X"

/-- `p.eval a` evaluates the polynomial `p` at the point `a`, substituting
`a` for the variable `X`. -/
DefinitionDoc Polynomial.eval as "eval"

/- Evaluating the polynomial `X ^ 2 + 1` at `2` gives `5`. -/
Statement : (X ^ 2 + 1 : ℝ[X]).eval 2 = 5 := by
  Hint "[Hint tkwd] `simp` knows how evaluation interacts with `+`, `^`, `X`
  and constants."
  simp_log
  Hint "[Hint phzv] What remains is ordinary arithmetic — `grind` closes it."
  grind

NewDefinition Polynomial Polynomial.X Polynomial.eval
