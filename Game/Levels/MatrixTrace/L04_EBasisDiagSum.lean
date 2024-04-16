import Game.Levels.MatrixTrace.L03_MatrixEqSum

World "Trace"
Level 4

Title "Matrix"

Introduction
"
`stdBasisMatrix i j c` spans the vector space of matrices of a given size.
This is witnessed by `matrix_eq_sum_std_basis`. In this level, you will show
that the identity matrix is the sum of the matrices `E i i`.

"

open Nat Matrix BigOperators StdBasisMatrix



    -- around Matrices/level 2: introduce E_ij-version of Matrix.StdBasisMatrix.mul_of_ne,
    -- prove it in one line via mathlib, and use it in level 7.
    -- Matrices/level 3, sum not displayed: already fixed in mathlib


-- -- Not used later on in our proofs, but possibly useful and can be safely
-- -- removed, or given as a hint
-- lemma tmp0 {n : ℕ} {i : Fin n} :
--     E i i = stdBasisMatrix i i ((1 : Mat[n,n][ℝ]) i i) := by
--   rw [one_apply]
--   unfold E
--   simp?

Statement Matrix.ebasis_diag_sum_eq_one {n : ℕ} : ∑ i : Fin n, E i i = 1 := by
  rw [matrix_eq_sum_ebasis 1] -- Lvl 3
  congr
  ext i r s
  -- have h : {i} ⊆ (Finset.univ : Fin n) := Finset.subset_univ {i}
  rw [← Finset.sum_subset (Finset.subset_univ {i})]
  · simp
  · intro x h₁ h₂
    clear h₁ -- not needed
    rw [Matrix.one_apply]
    have h₃ : i ≠ x
    · simp at h₂
      symm
      assumption
    rw [if_neg h₃]
    simp

NewTheorem Matrix.one_apply Finset.mem_singleton

TheoremTab "Matrix"
