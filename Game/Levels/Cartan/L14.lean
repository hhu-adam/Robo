import Game.Metadata
import Mathlib.Topology.LocallyConstant.Basic

World "Cartan"
Level 14

open Topology Filter

Statement {f g : ℝ → ℝ} {x : ℝ} (hf : IsLocallyConstant f) (hg : IsLocallyConstant g)
    (h : f x = g x) : ∀ᶠ y in 𝓝 x, f y = g y := by
  have : ∀ᶠ y in 𝓝 x, f y = f x := by
    apply IsLocallyConstant.eventually_eq hf x
  rw [h] at this
  filter_upwards [this, IsLocallyConstant.eventually_eq hg x]
  intro y h1 h2
  rw [h1, h2]
