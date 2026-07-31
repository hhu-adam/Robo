import Game.Metadata


World "Hamel"
Level 9

open Finsupp FullGrind

/- This level shows a *dependent* pair: `g = 3 * f`, so `![f, g]` is **not**
linearly independent. -/

Statement :
    let f : ℝ → ℝ := fun x ↦ x + 2
    let g : ℝ → ℝ := fun x ↦ 3 * x + 6
    ¬ LinearIndependent ℝ ![f, g] := by
  Hint "[Hint rmlIpiff] Remember `Fintype.linearIndependent_iff`. "
  rw [Fintype.linearIndependent_iff]
  suffices h : ∃ s : Fin 2 → ℝ, ∑ i : Fin 2, s i • ![f, g] i = 0 ∧
    ∃ i, s i ≠ 0
  · push Not
    assumption
  use ![3, -1]
  simp_log
  funext x
  simp [f, g]
  ring

TheoremTab "LinearAlgebra"
