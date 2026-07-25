import Game.Metadata
import Mathlib.Topology.LocallyConstant.Basic

World "Cartan"
Level 13

open Topology Filter

Statement {f g : ℝ → ℝ} {x : ℝ} (hf : IsLocallyConstant f) (hg : IsLocallyConstant g)
    (h : f x = g x) : ∀ᶠ y in 𝓝 x, f y = g y := by
  Hint (strict := true) "[Hint c13f] First, establish `∀ᶠ y in 𝓝 x, f y = f x` by `have`. Remember the proof
    in the previous level. "
  have he1 : ∀ᶠ y in 𝓝 x, f y = f x := by
    have ho : IsOpen (f ⁻¹' {f x}) := by
      apply hf
    filter_upwards [IsOpen.eventually_mem ho rfl]
    intro y hy
    assumption
  Hint (strict := true) "[Hint pyos] Perfect! You are on track. You can also prove similar result for function `g`. "
  have he2 : ∀ᶠ y in 𝓝 x, g y = g x := by
    have ho : IsOpen (g ⁻¹' {g x}) := by
      apply hg
    filter_upwards [IsOpen.eventually_mem ho rfl]
    intro y hy
    assumption
  Hint (strict := true) "[Hint rhhe1] Try to `rw` {h} at {he1}."
  rw [h] at he1
  Hint (hidden := true) "[Hint fuhe2] Now, `filter_upwards [{he1}, {he2}]`."
  filter_upwards [he1, he2]
  intro y h1 h2
  rw [h1, h2]
