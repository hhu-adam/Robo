import Game.Metadata


World "Hamel"
Level 8

open Finsupp

/- *Linear independence of three vectors*: the monomials `1`, `x`, `x ^ 2`. -/

/---/
TheoremDoc Fintype.linearIndependent_iff as "Fintype.linearIndependent_iff" in "LinearAlgebra"

/---/
TheoremDoc linearIndependent_iff' as "linearIndependent_iff'" in "LinearAlgebra"

/---/
TheoremDoc Fin.sum_univ_three as "Fin.sum_univ_three" in "LinearAlgebra"

Statement :
    let f : ℝ → ℝ := fun x ↦ 1
    let g : ℝ → ℝ := fun x ↦ x
    let h : ℝ → ℝ := fun x ↦ x ^ 2
    LinearIndependent ℝ ![f, g, h] := by
  Hint "[Hint lI3iff] Rewrite the goal with `Fintype.linearIndependent_iff`: the
    three functions are linearly independent iff every vanishing combination
    `c 0 • f + c 1 • g + c 2 • h = 0` forces all three coefficients to be zero.
    `Fin.sum_univ_three` writes the sum out."
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [Fin.sum_univ_three] at hc
  Hint "[Hint ev3pts] `{hc}` is an equality of *functions*. A quadratic is
    determined by its values at three points, so evaluate at three of them and
    solve the resulting linear system for the coefficients."
  Hint (hidden := true) "[Hint ev3cong] Use `congrFun` at the points `0`, `1`
    and `-1`."
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc (-1)
  simp [f, g, h] at h0 h1 h2
  have hc0 : c 0 = 0 := by grind
  have hc1 : c 1 = 0 := by grind
  have hc2 : c 2 = 0 := by grind
  intro i
  fin_cases i
  · grind
  · grind
  · grind

NewTheorem Fintype.linearIndependent_iff linearIndependent_iff' Fin.sum_univ_three

TheoremTab "LinearAlgebra"
