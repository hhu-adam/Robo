import Game.Levels.MatrixTrace.L05_EBasisEqOnDiag

World "Trace"
Level 6

Title "Kommutator"

Introduction
"
Gleich neben dem Baum findest du auch noch eine Notiz in der gross `E i j` durchgestrichen ist.

**Du**: Merkwürdig, die diagonalen `E i i` sind ihm alle gleich, die anderen `E i j` interessieren
es nicht.

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
  Hint "**Robo**: Wie könnten wir ich denn `{h₁}` hier verwenden?

  **Du**: Wie wär's damit, wenn wir `E i j` als `E i j * E j j` aufteilen, und dann kommutieren, denn die Umkehrung
  `E j j * E i j` sollte `0` sein!

  **Robo*: Wenn du meinst. Du kannst diese Gleichung mit einem Zwischenschritt
  `f (E i j) = f (E i j * E j j) = 0` lösen, dann kannst du `trans f (E i j * E j j)`
  verwenden.
  "
  trans f (E i j * E j j)
  · Hint (hidden := true) "**Du**: Ehm, das sehe ich einfach von der Definition.

    **Robo**: Vergiss nicht, dass du `unfold E` angeben musst oder alternative `simp [E]`."
    simp [E]
  · Hint "**Robo**: Und hier wolltest du jetzt kommutieren?

    **Du**: Genau! Schau:"
    rw [h₁]
    Hint "**Robo**: Das hatten wir auf dem zweiten Pergamentstück, das wir gefunden haben!"
    Hint (hidden := true) "**Robo**: Das hiess `E.mul_of_ne`."
    rw [E.mul_of_ne] -- Lvl 2
    · simp
    · symm
      assumption

NewTheorem Matrix.E.mul_of_ne
TheoremTab "Matrix"
