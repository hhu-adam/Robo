import Game.Metadata
import Mathlib.Analysis.Calculus.Deriv.Slope

World "Slope"
Level 10

open Topology Filter FullGrind

/---/
TheoremDoc hasDerivAt_iff_tendsto_slope as "hasDerivAt_iff_tendsto_slope" in "Function"

/---/
TheoremDoc tendsto_nhdsWithin_congr as "tendsto_nhdsWithin_congr" in "Function"

Statement {x : ℝ} :
    let f : ℝ → ℝ := fun x ↦ x ^ 2
    HasDerivAt f (2 * x) x  := by
  Hint "[Hint aes3a] `HasDerivAt f x` means what you think it means.  Unfold it with
  `hasDerivAt_iff_tendsto_slope`"
  rw [hasDerivAt_iff_tendsto_slope]
  Hint (strict := true) "[Hint l49nj] We computed this slope earlier. Reproduce it here with `have`:
  `have : ∀ y ∈ ({x} : Set ℝ)ᶜ …`"
  have h : ∀ y ∈ ({x} : Set ℝ)ᶜ , y + x = slope f x y := by
    intro y hy
    rw [slope_def_field]
    grind
    /-
    TODO: This does not work in the browser.
    -/
  Hint (strict := true) "[Hint m8bkd] Excellent.  Now can use following fact:
    if two functions `f` and `g` agree on some set `s`, and the values of `f`
    along some sequence in `s` converge, then the values of `g` along that
    sequence also converge, and to the same value.
    This is `tendsto_nhdsWithin_congr`.
    `apply` it with the equality of functions {h} as hypothesis."
  /-
  TODO: investigate why this hint is not displayed
        also, next line does not work in browser
        something wrong here
  -/
  apply tendsto_nhdsWithin_congr h
  Hint (strict := true) "[Hint bs7xd] Now compute the limit of `y ↦ y + x` at `x`.
    Start with `have : Tendsto (fun y : ℝ ↦ y + x) (𝓝 x) (𝓝 …)"
  Hint (strict := true) (hidden := true) "[Hint bs7xd] `(𝓝 (2 * x))`"
  have : Tendsto (fun y : ℝ ↦ y + x) (𝓝 x) (𝓝 (2 * x)) := by
    Hint "[Hint tscyx] Notice that $f(y) = y + x$ is continuous.
    Remember `Continuous.tendsto'`."
    apply Continuous.tendsto'
    · fun_prop
    · ring
  Hint (hidden := true) "[Hint bs7xd] Remember `Tendsto.mono_left`"
  apply Tendsto.mono_left this
  apply nhdsWithin_le_nhds

NewTheorem hasDerivAt_iff_tendsto_slope tendsto_nhdsWithin_congr
NewDefinition HasDerivAt
