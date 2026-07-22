import Game.Metadata


World "Step"
Level 9

open Finsupp

/- This level shows a *dependent* pair: `g = 3 * f`, so `![f, g]` is **not**
linearly independent. -/

Statement :
    let f : ℝ → ℝ := fun x ↦ x + 2
    let g : ℝ → ℝ := fun x ↦ 3 * x + 6
    ¬ LinearIndependent ℝ ![f, g] := by
  Hint "[Hint rmlIpiff] Remember `LinearIndependent.pair_iff`. "
  rw [LinearIndependent.pair_iff]
  intro H
  have heq : (3 : ℝ) • f + (-1 : ℝ) • g = 0 := by
    funext x
    simp [f, g]
    ring
  grind

TheoremTab "LinearAlgebra"
