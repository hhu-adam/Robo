import Game.Levels.MatrixTrace.L05_EBasisEqOnDiag

World "Trace"
Level 6

Title "Matrix"

Introduction
"
In this level, we will show that a linear functional `f` on the space of matrices which kills all commutators also kills all off-diagonal elementary basis matrices.
"

open Nat Matrix BigOperators StdBasisMatrix

Statement Matrix.zero_on_offDiag_ebasis {n : ℕ} {f : Mat[n,n][ℝ] →ₗ[ℝ] ℝ}
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
    unfold E
    simp
  · Hint "**Robo**: …und dann die Zweite."
    rw [h₁]
    Hint "`E.mul_of_ne`"
    rw [E.mul_of_ne] -- Lvl 2
    simp
    symm
    assumption

NewTheorem Matrix.E.mul_of_ne
TheoremTab "Matrix"
