import Game.Levels.MatrixTrace.L02_EBasis

World "Trace"
Level 3

Title "Matrix"

Introduction ""

Conclusion ""

open Nat Matrix BigOperators StdBasisMatrix

/-- Sagt aus, dass man jede $(n × n)$-Matrix (über $\mathbb{R}$) $A$ schreiben kann
als $A = \sum_{i=0}^{n-1}\sum_{j=0}^{n-1} A_{ij} \cdot E(i, j)$.

Siehe auch `matrix_eq_sum_std_basis`, welches die generalisierte Form für
$(m × n)$-Matrix (über beliebigem $R$) ist. -/
TheoremDoc Matrix.matrix_eq_sum_ebasis as "matrix_eq_sum_ebasis" in "Matrix"

/-- Die generellere Version von `matrix_eq_sum_ebasis`. Siehe dort. -/
TheoremDoc Matrix.matrix_eq_sum_std_basis as "matrix_eq_sum_std_basis" in "Matrix"

Statement Matrix.matrix_eq_sum_ebasis {n : ℕ} (A : Mat[n,n][ℝ]) :
    A = ∑ i : Fin n, ∑ j : Fin n, (A i j) • E i j := by
  Hint "**Du**: Da kann ich ja gleich das anwenden, was wir soeben gemacht haben."
  Hint (hidden := true) "**Robo**: Unter Summen braucht man `simp_rw`."
  simp_rw [Matrix.smul_ebasis] -- Lvl 1
  Hint "**Robo**: Diese Form kenne ich aus meiner Bibliothek, das ist
  `apply matrix_eq_sum_std_basis`."
  apply matrix_eq_sum_std_basis

NewTheorem Matrix.matrix_eq_sum_std_basis
TheoremTab "Matrix"
