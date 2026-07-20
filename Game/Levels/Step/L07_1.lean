import Game.Metadata


World "Step"
Level 8

open Finsupp

/- **Linear independent for three vectors**: I not sure we should add this to the main story. -/

/- This level shows a *dependent* pair: `g = 3 * f`, so `![f, g]` is **not**
linearly independent. -/

Statement :
    let f : ℝ → ℝ := fun x ↦ 1
    let g : ℝ → ℝ := fun x ↦ x
    let h : ℝ → ℝ := fun x ↦ x ^ 2
    LinearIndependent ℝ ![f, g, h] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [Fin.sum_univ_three] at hc
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc (-1)
  simp_log [f, g, h] at h0 h1 h2
  have hc0 : c 0 = 0 := by grind
  have hc1 : c 1 = 0 := by grind
  have hc2 : c 2 = 0 := by grind
  intro i
  fin_cases i
  · grind
  · grind
  · grind
