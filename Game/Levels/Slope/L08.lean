import Game.Metadata

World "Slope"
Level 8

open Topology Filter

/---/
TheoremDoc tendsto_nhds_unique as "tendsto_nhds_unique" in "Function"

Statement (f : ℝ → ℝ) (a b : ℝ) (h₁ : Tendsto f (𝓝 0) (𝓝 a))
    (h₂ : Tendsto f (𝓝 0) (𝓝 b)) : a = b := by
  Hint "[Hint tnu] A function cannot approach two different values along the
    same approach: limits are unique. This is the theorem
    `tendsto_nhds_unique`; apply it using `h₁` and `h₂`."
  apply tendsto_nhds_unique h₁ h₂

NewTheorem tendsto_nhds_unique
