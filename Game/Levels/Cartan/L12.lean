import Game.Metadata
import Mathlib.Topology.LocallyConstant.Basic

World "Cartan"
Level 12

open Topology Filter

Statement {g₁ g₂ g₃ : ℝ → ℝ} {x : ℝ} {f : Filter ℝ}
    (h1 : g₁ =ᶠ[f] g₂) (h2 : g₂ =ᶠ[f] g₃) : g₁ =ᶠ[f] g₃ := by
  /- Althought we can prove this statement by h1.trans h2. -/
  filter_upwards [h1, h2]
  intro y hy1 hy2
  rw [hy1, hy2]
