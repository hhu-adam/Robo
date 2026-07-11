import Game.Metadata




import Game.Levels.MatrixSpan.L11

World "Span"
Level 12

Title "" -- "Span"

/- # Introduction

The universal property of the submodule `Submodule.span K S`  spanned by a set
`S : Set M` is that `x ∈ Submodule.span K S` iff `x ∈ P` for any submodule `P`
containing `S`.

-/

open Real Function Set Finset

lemma powers_span_commute {n : ℕ} {A : Mat[n,n][ℝ]}
    {X Y : Mat[n,n][ℝ]} (hX : X ∈ Submodule.span ℝ (Submonoid.powers A))
    (hY : Y ∈ Submodule.span ℝ (Submonoid.powers A)) : X * Y = Y * X := by
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
