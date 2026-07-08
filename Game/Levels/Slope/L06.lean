import Game.Metadata
import Mathlib.Analysis.Calculus.Deriv.Slope

World "Slope"
Level 6

open Topology Filter

/---/
TheoremDoc Filter.Tendsto.mono_left as "Tendsto.mono_left" in "Function"

/---/
TheoremDoc nhdsWithin_le_nhds as "nhdsWithin_le_nhds" in "Function"

/---/
TheoremDoc hasDerivAt_iff_tendsto_slope as "hasDerivAt_iff_tendsto_slope" in "Function"

/---/
TheoremDoc tendsto_nhdsWithin_congr as "tendsto_nhdsWithin_congr" in "Function"

/---/
DefinitionDoc HasDerivAt as "HasDerivAt" in "Function"

Statement {x : ℝ} :
    let f : ℝ → ℝ := fun x ↦ x ^ 2
    HasDerivAt f (2 * x) x  := by
  rw [hasDerivAt_iff_tendsto_slope]
  have : ∀ y ∈ ({x} : Set ℝ)ᶜ , y + x = slope f x y := by
    intro y hy
    rw [slope_def_field]
    grind
  apply tendsto_nhdsWithin_congr this
  have h : Tendsto (fun y : ℝ ↦ y + x) (𝓝 x) (𝓝 (2 * x)) := by
    Hint "[Hint tscyx] Notice that $f(y) = y + x$ is continuous and the
    theorem `Continuous.tendsto'`."
    apply Continuous.tendsto'
    · fun_prop
    · ring
  apply h.mono_left
  apply nhdsWithin_le_nhds

NewTheorem Filter.Tendsto.mono_left nhdsWithin_le_nhds hasDerivAt_iff_tendsto_slope
  tendsto_nhdsWithin_congr
NewDefinition HasDerivAt
