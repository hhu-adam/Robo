import Game.Metadata
import Mathlib.Analysis.Calculus.Deriv.Slope

World "Slope"
Level 12

open Topology Filter

Statement (c : ℝ) :
    let f : ℝ → ℝ := fun x ↦ |x|
    ¬ HasDerivAt f c 0 := by
  Hint "[Hint absnd] Near `0`, the slope of `|x|` is `1` on the right but `-1`
    on the left — so no `c` works. Argue by contradiction and rewrite with
    `hasDerivAt_iff_tendsto_slope`. Then restrict the limit to one side first:
    `Tendsto (slope f 0) (𝓝[>] 0) (𝓝 c)`, where `𝓝[>] 0` (typed `\nhds[>]`)
    means approaching `0` from the right."
  by_contra h
  rw [hasDerivAt_iff_tendsto_slope] at h
  have e₁ : c = 1 := by
    have h₁ : Tendsto (slope f 0) (𝓝[>] 0) (𝓝 c) := by
      apply h.mono_left
      apply nhdsWithin_mono
      grind
    have slope_pos : ∀ x ∈ Set.Ioi 0, slope f 0 x = 1 := by
      intro y hy
      rw [slope_def_field]
      grind
    have aux : Tendsto (fun (x : ℝ) ↦ 1) (𝓝[>] 0) (𝓝 c) := by
      apply tendsto_nhdsWithin_congr slope_pos
      assumption
    apply tendsto_nhds_unique aux
    apply tendsto_const_nhds
  have e₂ : c = -1 := by
    have h₂ : Tendsto (slope f 0) (𝓝[<] 0) (𝓝 c) := by
      apply h.mono_left
      apply nhdsWithin_mono
      grind
    have slope_neg : ∀ x ∈ Set.Iio 0, slope f 0 x = -1 := by
      intro y hy
      rw [slope_def_field]
      grind
    have aux : Tendsto (fun (x : ℝ) ↦ -1) (𝓝[<] 0) (𝓝 c) := by
      apply tendsto_nhdsWithin_congr slope_neg
      assumption
    apply tendsto_nhds_unique aux
    apply tendsto_const_nhds
  grind
