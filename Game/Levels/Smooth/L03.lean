import Game.Metadata

World "Smooth"
Level 3

open Real Filter Topology

noncomputable section

Introduction " Intro Smooth L03:
Meet the star of this world: the *smooth take-off function*
$$
f(x) = \\begin{cases} 0 & \\text{if } x \\le 0 \\\\ e^{-1/x} & \\text{if } x > 0 \\end{cases}
$$
It is flat `0` on the left and rises as `exp (-x⁻¹)` on the right — the seam at `0`
is where all the interesting smoothness happens.

Start with the easy half: on the non-positive axis `f` is simply `0`.
"

/-- Smooth take-off function -/
def f : ℝ → ℝ := fun x ↦ if x ≤ 0 then 0 else exp (- x⁻¹)

/-- The smooth take-off function `f x = if x ≤ 0 then 0 else exp (-x⁻¹)`. -/
DefinitionDoc f as "f"

/-- On the non-positive axis the take-off function vanishes: `f x = 0` when `x ≤ 0`. -/
TheoremDoc zero_of_nonpos as "zero_of_nonpos"

/- On the non-positive axis the take-off function is `0`. -/
Statement zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : f x = 0 := by
  Hint "[Hint znp] This is just follows by definition."
  Branch
    unfold f
    Hint "[Hint smth3ts] Use `{hx}` to simplify the goal."
    simp [hx]
  Hint (hidden := true) "[Hint smthts3] Simplify the goal with input `{hx}`."
  simp [f, hx]

NewDefinition f
