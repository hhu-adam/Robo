import Game.Levels.MatrixTrace.L06_EvalOnEBasis

World "Matrix"
Level 7

Title "Matrix"

Introduction
"
In this level, we will show that a linear functional `f` on the space of matrices which kills all commutators also kills all off-diagonal elementary basis matrices.
"

open Nat Matrix BigOperators StdBasisMatrix

-- TODO: (JE) does it make sense to copy some API from `StdBasisMatrix` to  `E`?
-- @[inherit_doc Matrix.StdBasisMatrix.mul_of_ne]
theorem Matrix.E.mul_of_ne {n : ℕ} (i j : Fin n) {k l : Fin n} (h : j ≠ k) : E i j * E k l = 0 := by
  apply Matrix.StdBasisMatrix.mul_of_ne (h := h)

Statement Matrix.zero_on_offdiag_ebasis {n : ℕ} {f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) :
    ∀ (i j : Fin n ), (i ≠ j) → f (E i j) = 0 := by
  intro i j hne
  Hint "**Du**: Wie könnte ich denn `{h₁}` hier gut verwenden?

  **Du**: Wie wär's wenn ich `E i j` aufteile als `E i j * E j j`, denn die Umkehrung
  `E j j * E i j` sollte `0` sein!

  **Robo*: Wenn du meinst, du kannst diese Gleichung mit einem Zwischenschritt
  `f (E i j) = f (E i j * E j j) = 0` lösen, dann kannst du `trans f (E i j * E j j)`
  verwenden.
  "
  trans f (E i j * E j j)
  · Hint "**Robo**: Zuerst die erste der beiden Gleichungen…"
    rw [StdBasisMatrix.mul_same, mul_one]
  · Hint "**Robo**: … und dann die Zweite."
    rw [h₁]
    Hint "`E.mul_of_ne j j hne.symm`"
    rw [E.mul_of_ne j j hne.symm]
    simp

NewTheorem Matrix.E.mul_of_ne
TheoremTab "Matrix"
