import Game.Levels.MatrixTrace.L06_EBasisEqOnDiag

World "Trace"
Level 7

Title "Desinteresse"

Introduction
"
Gleich neben dem Baum findest du noch eine Notiz, in der groß `E i j` durchgestrichen ist.

**Du**: Soll wohl heißen: `E i j` mit i ≠ j interessieren nicht.

"

Conclusion "Die Spuren wirken mittlerweile viel frischer und ihr folgt ihnen schneller und
unvorsichtiger als zuvor."

open Nat Matrix BigOperators StdBasisMatrix

/---/
TheoremDoc Matrix.zero_on_offDiag_ebasis as "zero_on_offDiag_ebasis" in "Matrix"

Statement Matrix.zero_on_offDiag_ebasis {n : ℕ} {f : Mat[n,n][ℝ] →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) :
    ∀ (i j : Fin n ), (i ≠ j) → f (E i j) = 0 := by
  intro i j hne
  Hint "**Robo**: Wie könnten wir denn hier `{h₁}` verwenden?

  **Du**: Wie wär's, wenn wir diesmal `E i j` als Produkt `E i j * E j j` schreiben?

  **Robo**:  Wieso gerade so?

  **Du**: Wenn ich in diesem Produkt die Faktoren vertausche, erhalte ich Null!  Hatten wir doch auch schon, `E.mul_of_ne` oder so etwas."
  Hint (hidden := true) "**Robo*: Wie du meinst. Dann probier doch am besten `trans f (E i j * E j j)`."
  trans f (E i j * E j j)
  · Hint (hidden := true) "**Du**: Ehm, das sehe ich einfach von der Definition.

    **Robo**: Vergiss nicht `unfold E`, oder sag `simp`, dass es die Definition von `E` benutzen soll (`simp [E]`)."
    simp [E]
  · Hint "**Robo**: Und hier wolltest du jetzt kommutieren?

    **Du**: Genau!"
    rw [h₁]
    rw [E.mul_of_ne] -- Lvl 2
    · simp
    · symm
      assumption

NewTheorem Matrix.E.mul_of_ne
TheoremTab "Matrix"
