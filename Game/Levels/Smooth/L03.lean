import Game.Metadata
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

World "Smooth"
Level 3

open Real Filter Topology

noncomputable section

Introduction "
Meet the star of this world: the *smooth take-off function*
`f x = if x ≤ 0 then 0 else exp (-x⁻¹)`. It is flat `0` on the left and rises as
`exp (-x⁻¹)` on the right — the seam at `0` is where all the interesting
smoothness happens.

Start with the easy half: on the non-positive axis `f` is simply `0`.
"

/-- Smooth take-off function -/
def f : ℝ → ℝ := fun x ↦ if x ≤ 0 then 0 else exp (- x⁻¹)

/-- On the non-positive axis the take-off function vanishes: `f x = 0` when `x ≤ 0`. -/
TheoremDoc zero_of_nonpos as "zero_of_nonpos"

/- On the non-positive axis the take-off function is `0`. -/
Statement zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : f x = 0 := by
  Hint "[Hint znp] Unfold `f`; the hypothesis `hx : x ≤ 0` selects the `then`
    branch. `simp [f, hx]` does both at once."
  simp [f, hx]
