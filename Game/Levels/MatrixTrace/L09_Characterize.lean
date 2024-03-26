import Game.Levels.MatrixTrace.L08_EvalOnEBasis

World "Matrix"
Level 9

Title "Matrix"

Introduction
"
The trace as a map from the space of `n × n` matrices to the field of scalars has the following properties:
1. It is linear, witnessed by `traceLinear`.
2. The trace of a identity matrix is the dimension of the matrix, i.e.
`trace (1 : Matrix α α ℝ) = Fintype.card α`.
3. The matrices in the trace of a product can be switched without changing the result, i.e. `trace (A * B) = trace (B * A)`. This is witnessed by `trace_mul_comm`.

We show that these properties characterize the trace, that is any map satisfying these properties is equal to the trace.
"

open Nat Matrix BigOperators StdBasisMatrix Finset

Statement Matrix.trace_eq {n : ℕ} (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n) :
    trace = f := by
  Hint (hidden := true) "**Du**: Zwei Funktionen sind gleich wenn sie auf
  allen Elementen gleich sind…

  **Robo**: Das war `ext A`!"
  ext A
  Hint "**Du**: Hatten wir nicht eben gerade, dass `f {A}` also Summe über `{A} i j * f (E i j)`
  schreiben kann?

  **Robo**: Was du vorhin bewiesen hast, hies `eq_sum_apply_diag_ebasis`."
  Branch
    rw [eq_sum_apply_diag_ebasis (zero_on_offdiag_ebasis h₁)]
    rcases n
    · simp
    · simp_rw [eq_on_diag_ebasis h₁ _ 0] -- we dont need this statement
      rw [← sum_mul]
      rw [one_on_diag_ebasis h₁ h₂ 0]
      simp [trace]
  rw [eq_sum_apply_diag_ebasis] -- Lvl 5
  Hint "**Du**: Und jetzt? Stimmt das überhaupt für `n = 0`?

  **Robo**: Ja, die Spur einer 0×0-Matrix ist per Definition `0`!

  **Du**: Nah dann kann ich ja mal diesen Fall zuerst machen."
  Hint (hidden := true) "**Robo**: das war `rcases n`."
  rcases n
  · Hint (hidden := true) "
      **Robo**: Den Fall `n = 0` kann sogar ich! Ich wende einfach
      immer `simp` an und das Betriebsystem gibt ein wohliges Schnurren zurück."
    simp
  · Hint "**Du**: Wir hatten doch auch schon dass für unser `{f}` gilt dass `f (E i i) = 1`!

    **Robo**: Nachschlagen kann ich gut! Das war `one_on_diag_ebasis`."
    Hint (hidden := true) "**Robo**: Denk daran, unter einer Summe must du `simp_rw` verwenden,
    `rw` kann das nicht.

    **Du**: Ah, und die expliziten Argumente sollte ich wohl auch noch angeben."
    simp_rw [one_on_diag_ebasis h₁ h₂] -- Lvl 8
    Hint (hidden := true) "**Du** Jetzt `mul_one`?"
    simp_rw [mul_one]
    Hint "**Robo**: Die beiden sind per Definition gleich!"
    rfl
  Hint "**Du**: Wo kommt denn das her?

  **Robo**: Ganz am Anfang bei `rw [eq_sum_apply_diag_ebasis]` hast du vermutlich dieses Argument
  ausgelassen, jetzt kannst du es noch nachholen."
  intro i j hij
  Hint "**Du**: Robo, wie hies das nochmals, dass unser `{f}` ausserhalb der Diagonale null ist?

  **Robo**: `zero_on_offdiag_ebasis`."
  apply zero_on_offdiag_ebasis -- Lvl 7
  assumption
  assumption

TheoremTab "Matrix"
