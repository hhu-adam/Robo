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
  Hint (hidden := true) "[Hint ftys1] First, try to prove that `c = 1`. "
  have e₁ : c = 1 := by
    have hc : Tendsto (slope f 0) (𝓝[>] 0) (𝓝 c) := by
      Hint (hidden := true) "[Hint y8g14] Good intermediate step"
      apply h.mono_left
      apply nhdsWithin_mono
      grind
    have pos_slope : ∀ x ∈ Set.Ioi 0, 1 = slope f 0 x := by
      Hint (hidden := true) "[Hint bp7a2] Good intermediate step"
      intro y hy
      rw [slope_def_field]
      grind
    have h1 : Tendsto (slope f 0) (𝓝[>] 0) (𝓝 1) := by
      Hint (hidden := true) "[Hint s9i5u] Good intermediate step"
      apply tendsto_nhdsWithin_congr pos_slope
      apply tendsto_const_nhds
    apply tendsto_nhds_unique hc h1
  Hint "[Hint ftysn1] Perfect! You're on track. Now, you can prove `c = -1` by similar process."
  have e₂ : c = -1 := by
    have hc : Tendsto (slope f 0) (𝓝[<] 0) (𝓝 c) := by
      apply h.mono_left
      apply nhdsWithin_mono
      grind
    have neg_slope : ∀ x ∈ Set.Iio 0, -1 = slope f 0 x := by
      intro y hy
      rw [slope_def_field]
      grind
    have h1 : Tendsto (slope f 0) (𝓝[<] 0) (𝓝 (-1)) := by
      apply tendsto_nhdsWithin_congr neg_slope
      apply tendsto_const_nhds
    apply tendsto_nhds_unique hc h1
  grind
