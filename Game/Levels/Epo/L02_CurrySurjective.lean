import Game.Metadata


World "Epo"
Level 2

Title ""

Introduction ""

open Function Nat

#check ne_comm

Statement {A B : Type} (f : ℕ → A → B) : ¬ Surjective f ↔ ∃ g : A → B, ∀ n, g ≠ f n := by
  Hint "
  **Du**:  `ℕ → A → B` … wie lese ich diese zwei Pfeile hintereinander?

  **Robo**: Du liest das als `ℕ → (A → B)` – eine Abbildung von den natürlichen Zahlen `ℕ` in die Menge `A → B` der Abbildungen von A nach B.  Das wird übringens auch klar, wenn du weiterliest, was du hier zeigen solltst."
  Hint (hidden := true) "
  **Robo**: Du könnstest mit `constructor` anfangen, oder du fängst an mit `unfold Surjective` und schaust dann, ob dich `push_neg` weiterbringt."
  Branch
    constructor
    · intro h
      simp [Surjective] at h
      push_neg at h
      obtain ⟨w, hw⟩ := h
      use w
      intro n
      Hint "
      **Robo**: Hilft dir vielleicht `ne_comm` weiter?
      Die Aussage von `ne_comm` ist `a ≠ b ↔ b ≠ a`."
      rw [ne_comm]
      apply hw
    · intro ⟨g, hg⟩
      intro hf
      obtain ⟨n, hn⟩ := hf g
      apply hg n
      symm
      assumption
  unfold Surjective
  push_neg
  Hint "
  **Robo**: Hilft dir vielleicht `ne_comm` weiter?
  Die Aussage von `ne_comm` ist `a ≠ b ↔ b ≠ a`.
  "
  Hint (hidden := true) "
  **Robo**: Wegen der vielen Quantoren funktioniert `rw [ne_comm]` hier nicht.
  Probier stattdessen mal `simp [ne_comm]`.
  "
  simp [ne_comm]

/---/
TheoremDoc ne_comm as "ne_comm" in "Logic"
NewTheorem ne_comm
-- NewConcept: Multivariate functions
