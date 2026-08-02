import Game.Metadata

World "Hamel"
Level 8

open Finsupp

/- *Old level 8* (`O08`), kept for reference and **not** imported by `Game/Levels/Hamel.lean`:
the pair version of the current level 8, which does the same for three vectors. -/

/---/
TheoremDoc LinearIndependent.pair_iff as "LinearIndependent.pair_iff" in "LinearAlgebra"

/---/
TheoremDoc linearIndependent_iff' as "linearIndependent_iff'" in "LinearAlgebra"

Statement :
    let f : ℝ → ℝ := fun x ↦ x + 2
    let g : ℝ → ℝ := fun x ↦ x - 3
    LinearIndependent ℝ ![f, g] := by
  Hint "[Hint lIpiff] Rewrite the goal with `LinearIndependent.pair_iff`: two
    vectors are linearly independent iff `s • f + t • g = 0` forces
    `s = 0 ∧ t = 0`."
  rw [Fintype.linearIndependent_iff]
  intro s h
  Hint "[Hint apcongF] `h` is an equality of *functions* — evaluate it at `0`
    and `1` with `congrFun`."
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [f, g] at h0 h1
  intro i
  fin_cases i
  · grind
  · grind

NewTheorem linearIndependent_iff'

TheoremTab "LinearAlgebra"
