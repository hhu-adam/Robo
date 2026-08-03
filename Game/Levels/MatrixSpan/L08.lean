import Game.Metadata
import Game.Levels.MatrixSpan.L07

World "Span"
Level 8

Introduction "Intro Span L08"

open Real Function Set Finset

/-- `powers_span_commute` : any two elements of `Submodule.span ℝ (Submonoid.powers A)` commute. -/
TheoremDoc powers_span_commute as "powers_span_commute" in "LinearAlgebra"

Statement powers_span_commute {n : ℕ} {A : Mat[n,n][ℝ]}
    {X Y : Mat[n,n][ℝ]} (hX : X ∈ Submodule.span ℝ (Submonoid.powers A))
    (hY : Y ∈ Submodule.span ℝ (Submonoid.powers A)) : X * Y = Y * X := by
  Hint "[Hint sp8ind2] Commuting survives sums and scalar multiples, so it is enough to
    check it on the spanning set. `Submodule.span_induction₂` performs exactly this
    induction in both arguments."
  Branch
    -- Alternative: induct on `X` and `Y` separately with `Submodule.span_induction`,
    -- reducing to the base case `powers_commute`.
    induction hX using Submodule.span_induction with
    | mem X hX =>
        induction hY using Submodule.span_induction with
        | mem Y hY => apply powers_commute X Y hX hY
        | zero => rw [mul_zero, zero_mul]
        | add Y₁ Y₂ _ _ iY₁ iY₂ => rw [mul_add, add_mul, iY₁, iY₂]
        | smul c Y _ iY => rw [mul_smul_comm, smul_mul_assoc, iY]
    | zero => rw [zero_mul, mul_zero]
    | add X₁ X₂ _ _ iX₁ iX₂ => rw [add_mul, mul_add, iX₁, iX₂]
    | smul c X _ iX => rw [smul_mul_assoc, mul_smul_comm, iX]
  Hint (hidden := true) "[] Try to `apply Submodule.span_induction₂ _ _ _ _ _ _ _ {hX} {hY}`."
  apply Submodule.span_induction₂ _ _ _ _ _ _ _ hX hY
  · intro B C hB hC
    Hint (hidden := true) "[] Remember the theorem `powers_commute` in the previous levels."
    apply powers_commute B C hB hC
  · intro Z _
    simp
  · intro Z _
    simp
  · intro D E F _ _ _ hDF hEF
    rw [add_mul, mul_add, hDF, hEF]
  · intro D E F _ _ _ hDE hDF
    rw [mul_add, add_mul, hDE, hDF]
  · intro c D E _ _ hDE
    Hint "[Hint sp8smul] A scalar can be pulled out of a product from either side:
      `smul_mul_assoc` says `({c} • {D}) * {E} = {c} • ({D} * {E})`, and `mul_smul_comm` says
      `{D} * ({c} • {E}) = {c} • ({D} * {E})`."
    rw [smul_mul_assoc, mul_smul_comm, hDE]
  · intro c D E _ _ hDE
    rw [mul_smul_comm, smul_mul_assoc, hDE]

/---/
TheoremDoc smul_mul_assoc as "smul_mul_assoc" in "+ *"

/---/
TheoremDoc mul_smul_comm as "mul_smul_comm" in "+ *"

/---/
TheoremDoc Submodule.span_induction₂ as "Submodule.span_induction₂" in "LinearAlgebra"

NewTheorem smul_mul_assoc mul_smul_comm Submodule.span_induction₂

TheoremTab "LinearAlgebra"
