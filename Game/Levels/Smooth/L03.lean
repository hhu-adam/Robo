import Game.Metadata

World "Smooth"
Level 3

open Real Filter Topology

noncomputable section

Introduction "Intro Smooth L03"

namespace STakeOff

/-- Smooth take-off function -/
def f : ℝ → ℝ := fun x ↦ if x ≤ 0 then 0 else exp (- x⁻¹)

/-- The smooth take-off function `f x = if x ≤ 0 then 0 else exp (-x⁻¹)`. -/
DefinitionDoc STakeOff.f as "f"

/-- On the non-positive axis the take-off function vanishes: `f x = 0` when `x ≤ 0`. -/
TheoremDoc STakeOff.zero_of_nonpos as "zero_of_nonpos"

/- On the non-positive axis the take-off function is `0`. -/
Statement zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : f x = 0 := by
  Hint "[Hint smth3f] The *smooth take-off function* is
    $$
    f(x) = \\begin\{cases}
      0 & \\text\{if } x \\le 0, \\\\ %(new line)
      e^\{-1/x} & \\text\{if } x > 0.
    \\end\{cases}
    $$
    It is flat `0` on the left and rises as `exp (-x⁻¹)` on the right — the seam at `0` is
    where all the interesting smoothness happens."
  Hint "[Hint znp] On the left of the seam there is nothing to compute: unfolding `f`, the
    assumption `{hx}` picks the first branch of the `if`."
  Branch
    unfold f
    Hint "[Hint smth3ts] Use `{hx}` to simplify the goal."
    simp [hx]
  Hint (hidden := true) "[Hint smthts3] `simp [f, {hx}]` unfolds and simplifies in one go."
  simp [f, hx]

NewDefinition STakeOff.f
