import Game.Metadata


World "FunctionSurj"
Level 2

Title "Not exhausted by naturals."

Introduction
"
**Robo**: Du hast zwei Möglichkeiten, entweder du kannst mit `constructor` anfangen,
oder du machst mal `unfold Surjective` und schaust dann, ob `push_neg` was kann.

**Robo**: Btw, Ich glaube `ne_comm`, welches `a ≠ b ↔ b ≠ a` sagt, könnte hier nützlich sein.
"

open Function Nat

#check ne_comm

Statement {A B : Type} (f : ℕ → A → B) : ¬ Surjective f ↔ ∃ g : A → B, ∀ n, g ≠ f n := by
  Branch
    constructor
    · intro h
      simp [Surjective] at h
      push_neg at h
      obtain ⟨w, hw⟩ := h
      use w
      intro n
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
  simp_rw [ne_comm]

NewTheorem ne_comm
-- NewConcept: Multivariate functions
