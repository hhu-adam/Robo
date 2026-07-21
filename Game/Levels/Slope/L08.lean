import Game.Metadata
import Mathlib.LinearAlgebra.AffineSpace.Slope

World "Slope"
Level 8

open Topology Filter Metric

/- TODO: Should we keep this level. -/

/---/
TheoremDoc Metric.tendsto_nhdsWithin_nhds as "tendsto_nhdsWithin_nhds" in "Function"

/---/
TheoremDoc Real.dist_eq as "Real.dist_eq" in "Function"

Statement :
    Tendsto (fun (x : ℝ) => if x = 0 then 1 else |x|) (𝓝[≠] 0) (𝓝 0) := by
  Hint "[Hint epsdel] This function is not continuous at `0` (its value there
    is `1`), so the previous strategy fails. Instead, use `tendsto_nhdsWithin_nhds`
    to turn the goal into a familiar ε-δ statement."
  apply tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  use ε
  constructor
  · assumption
  · intro x hx hx'
    have hx0 : x ≠ 0 := hx
    rw [if_neg hx0]
    rw [Real.dist_eq] at ⊢ hx'
    grind

NewTheorem Metric.tendsto_nhdsWithin_nhds Real.dist_eq
