import Game.Metadata
import Mathlib.Analysis.Calculus.Deriv.Slope

World "Slope"
Level 11

open Topology Filter FullGrind

Statement (c : ℝ) :
    let f : ℝ → ℝ := fun x ↦ |x|
    ¬ HasDerivAt f c 0 := by
  Hint "[Hint absnd] Near `0`, the slope of `|x|` is `1` on the right but `-1`
    on the left — so no `c` works. Argue by contradiction and rewrite with
    `hasDerivAt_iff_tendsto_slope`."
  by_contra h
  rw [hasDerivAt_iff_tendsto_slope] at h
  /- TODO:
    Put some encouraing hints in this level.
    Perhaps list of have statements in natural luangage?
    And at the beginning of the proof of each have statement,
    a hint saying "you're on track"
    *Resolved*
  -/
  Hint (hidden := true) "[Hint ftys1] First, try to prove that `c = 1`. "
  have e₁ : c = 1 := by
    have hc : Tendsto (slope f 0) (𝓝[>] 0) (𝓝 c) := by
      apply h.mono_left
      apply nhdsWithin_mono
      grind
    have slope_pos : ∀ x ∈ Set.Ioi 0, 1 = slope f 0 x := by
      intro y hy
      rw [slope_def_field]
      grind
    have h1 : Tendsto (slope f 0) (𝓝[>] 0) (𝓝 1) := by
      apply tendsto_nhdsWithin_congr slope_pos
      apply tendsto_const_nhds
    apply tendsto_nhds_unique hc h1
  Hint "[Hint ftysn1] Perfect! You're on track. Now, you can also prove that `c = -1` by similar process."
  have e₂ : c = -1 := by
    have hc : Tendsto (slope f 0) (𝓝[<] 0) (𝓝 c) := by
      apply h.mono_left
      apply nhdsWithin_mono
      grind
    have slope_neg : ∀ x ∈ Set.Iio 0, -1 = slope f 0 x := by
      intro y hy
      rw [slope_def_field]
      grind
    have h1 : Tendsto (slope f 0) (𝓝[<] 0) (𝓝 (-1)) := by
      apply tendsto_nhdsWithin_congr slope_neg
      apply tendsto_const_nhds
    apply tendsto_nhds_unique hc h1
  grind
