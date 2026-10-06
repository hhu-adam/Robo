import Game.Levels.Smooth.L03

World "Smooth"
Level 4

open Real Filter Topology STakeOff Polynomial

Introduction "Intro Smooth L04a"

Statement (p : Polynomial ℝ) :
    (fun x ↦ p.eval x⁻¹ * f x) 0 = 0 := by
  Hint (hidden := true) "[Hint z5pfu] The convention in Lean is that `0⁻¹ = 0`"
  simp [f]

Conclusion "Conclusion Smooth L04: However, there is a real statement to be made."
