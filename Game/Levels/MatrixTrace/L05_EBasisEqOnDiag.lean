import Game.Levels.MatrixTrace.L04_EBasisDiagSum

World "Trace"
Level 5

Title "Matrix"

-- TODO: Intro & geschichte
Introduction
"
The commutator of two matrices is defined as the difference between their product and the product
of the matrices in the opposite order, that is the commutator of `A` and `B` is `A * B - B * A`.
A linear functional `f` on the space of `n × n` matrices which kills all commutators has the same value on all the diagonal elemantary basis matrices, i.e. `f (E i i) = f (E j j)` for all `i` and `j`.
"

open Nat Matrix BigOperators

Statement Matrix.eq_on_diag_ebasis {n : ℕ} {f : Mat[n,n][ℝ] →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A))  :
    ∀ (i j : Fin n), f (E i i) = f (E j j) := by
  intro i j
  Hint "**Du**: Wie kann ich denn wohl am besten die Annahme `{h}` brauchen, dazu müsste
  ich wohl zuerst eine Multiplikation haben.

  **Robo**: als was möchtest du denn `E i i` darstellen?

  ** Du**: Ich habe eine Idee: Man könnte `E i i = (E i j) * (E j i)` darstellen, das sollte gehen.

  **Robo**: Dann hab ich das Werkzeug dazu! Schreib `trans f (E i j * E j i)`, dann hast du zwei
  Goals `f (E i i) = f (E i j * E j i) = f (E j j)`, die du dann einzeln zeigen kannst.
  "
  trans f (E i j * E j i)
  · Hint (hidden := true) "**Du**: Diese erste Hälfte ist nur nachrechnen.

    **Robo**: Da `E` ganz konkret definiert ist, kann das `simp` bestimmt."
    unfold E
    simp
  · Hint (hidden := true) "**Robo**: Hast du das nicht alles gemacht, weil du `{h}` brauchen
    wolltest?

    **Du**: Ah ja, stimmt!"
    rw [h₁]
    unfold E
    simp

TheoremTab "Matrix"
NewTactic trans
