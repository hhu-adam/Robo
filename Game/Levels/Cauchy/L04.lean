import Game.Levels.Cauchy.L03

World "Cauchy"
Level 4

open Real Filter Topology Cauchy Polynomial

Introduction "Intro Cauchy L04a"

Statement (p : Polynomial ℝ) :
    (fun x ↦ p.eval x⁻¹ * f x) 0 = 0 := by
  Hint (hidden := true) "[Hint z5pfu] The convention in Lean is that `0⁻¹ = 0`"
  simp [f]

Conclusion "Conclusion Cauchy L04: However, there is a real statement to be made."
