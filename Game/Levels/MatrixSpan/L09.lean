import Game.Metadata




import Game.Levels.MatrixSpan.L08

World "Span"
Level 9

Title "" -- "Span"

/- # Introduction

The universal property of the submodule `Submodule.span K S`  spanned by a set
`S : Set M` is that `x ∈ Submodule.span K S` iff `x ∈ P` for any submodule `P`
containing `S`.

-/

open Real Function Set Finset

/-- `powers_span_commute` : any two elements of `Submodule.span ℝ (Submonoid.powers A)` commute. -/
TheoremDoc powers_span_commute as "powers_span_commute" in "LinearAlgebra"

Statement powers_span_commute {n : ℕ} {A : Mat[n,n][ℝ]}
    {X Y : Mat[n,n][ℝ]} (hX : X ∈ Submodule.span ℝ (Submonoid.powers A))
    (hY : Y ∈ Submodule.span ℝ (Submonoid.powers A)) : X * Y = Y * X := by
  Branch
    -- Alternative: induct on `X` and `Y` separately with `Submodule.span_induction`,
    -- reducing to the base case `powers_commute`.
    induction hX using Submodule.span_induction with
    | mem X hX =>
        induction hY using Submodule.span_induction with
        | mem Y hY => exact powers_commute X Y hX hY
        | zero => rw [mul_zero, zero_mul]
        | add Y₁ Y₂ _ _ iY₁ iY₂ => rw [mul_add, add_mul, iY₁, iY₂]
        | smul c Y _ iY => rw [mul_smul_comm, smul_mul_assoc, iY]
    | zero => rw [zero_mul, mul_zero]
    | add X₁ X₂ _ _ iX₁ iX₂ => rw [add_mul, mul_add, iX₁, iX₂]
    | smul c X _ iX => rw [smul_mul_assoc, mul_smul_comm, iX]
  apply Submodule.span_induction₂ _ _ _ _ _ _ _ hX hY
  · intro B C hB hC
    exact powers_commute B C hB hC
  · intro Z _
    rw [zero_mul, mul_zero]
  · intro Z _
    rw [mul_zero, zero_mul]
  · intro D E F _ _ _ hDF hEF
    rw [add_mul, mul_add, hDF, hEF]
  · intro D E F _ _ _ hDE hDF
    rw [mul_add, add_mul, hDE, hDF]
  · intro c D E _ _ hDE
    rw [smul_mul_assoc, mul_smul_comm, hDE]
  · intro c D E _ _ hDE
    rw [mul_smul_comm, smul_mul_assoc, hDE]

TheoremTab "LinearAlgebra"
