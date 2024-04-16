import Game.Levels.MatrixTrace.L06_EBasisZeroOffDiag

--import Game.StructInstWithHoles

World "Trace"
Level 7

Title "Matrix"

Introduction
"
A linear functional `f` on the space of `n × n` matrices (for non-zero `n`) which kills
all commutators and moreover satisfies `f(1) = n` has the property that `f (E i i) = 1`
for all `i : Fin n`.
"

open Nat Matrix BigOperators StdBasisMatrix Finset

/-- TODO: In Level 5 -/
TheoremDoc Matrix.eq_sum_apply_diag_ebasis as "eq_sum_apply_diag_ebasis" in "Matrix"


Statement Matrix.eq_sum_apply_diag_ebasis {n : ℕ} {f : Mat[n,n][ℝ] →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A))
    (A : Mat[n,n][ℝ]) :
    f A = ∑ i : Fin n, (A i i) * f (E i i) := by
  nth_rw 1 [matrix_eq_sum_ebasis A] -- Lvl 3
  -- simp [map_sum]
  simp
  trans ∑ i : Fin n, ∑ j : Fin n, if i = j then (A i j) * f (E i j) else 0
  · congr
    ext i
    congr
    ext j
    by_cases h₂ : i = j
    · rw [if_pos h₂]
    · rw [if_neg h₂]
      simp
      right
      apply Matrix.zero_on_offDiag_ebasis h₁ -- Lvl 6
      assumption
  · simp

TheoremTab "Matrix"
