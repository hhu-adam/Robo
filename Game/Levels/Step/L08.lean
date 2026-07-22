import Game.Metadata

World "Step"
Level 8

open Finsupp

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
  rw [LinearIndependent.pair_iff]
  intro s t h
  Hint "[Hint apcongF] `h` is an equality of *functions* — evaluate it at `0`
    and `1` with `congrFun`."
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp at h0 h1
  grind

NewTheorem LinearIndependent.pair_iff linearIndependent_iff'

TheoremTab "LinearAlgebra"
