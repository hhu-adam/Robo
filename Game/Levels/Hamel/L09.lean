import Game.Metadata

World "Hamel"
Level 9

Introduction "Intro Hamel L09"

open Finsupp FullGrind

/- This level shows a *dependent* pair: `g = 3 * f`, so `![f, g]` is **not**
linearly independent. -/

Statement :
    let f : ℝ → ℝ := fun x ↦ x + 2
    let g : ℝ → ℝ := fun x ↦ 3 * x + 6
    ¬ LinearIndependent ℝ ![f, g] := by

  Hint "[Hint rmlIpiff] The two functions are
    $$
    \\begin\{aligned}
      f &\\colon ℝ \\to ℝ, \\quad x \\mapsto x + 2, \\\\ %
      g &\\colon ℝ \\to ℝ, \\quad x \\mapsto 3x + 6.
    \\end\{aligned}
    $$"
  Hint (hidden := true) "[Hint rmlIpiffh] Remember `Fintype.linearIndependent_iff`."
  rw [Fintype.linearIndependent_iff]
  Branch
    suffices h : ∃ s : Fin 2 → ℝ, ∑ i : Fin 2, s i • ![f, g] i = 0 ∧
      ∃ i, s i ≠ 0
    · push Not
      assumption
  Hint (hidden := true) "[Hint lI2push] The goal is a negation, so `push Not` moves it inside:
    all you have to provide is one vanishing combination with a nonzero coefficient."
  push Not
  Hint (hidden := true) "[Hint lI2use] Since `g` is `3` times `f`, the coefficients `![3, -1]`
    do the job."
  use ![3, -1]
  simp
  funext x
  simp [f, g]
  ring

TheoremTab "LinearAlgebra"
