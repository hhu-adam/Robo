import Game.Metadata


World "Epo"
Level 2

Title "Not exhausted by naturals."

Introduction ""

open Function Nat

#check ne_comm

Statement {A B : Type} (f : ℕ → A → B) : ¬ Surjective f ↔ ∃ g : A → B, ∀ n, g ≠ f n := by
  Hint "**Robo**: Du könnstest mit `constructor` anfangen,
  oder du fängst an mit `unfold Surjective` und schaust dann, ob dich `push_neg` weiterbringt.
  So oder so könnte `ne_comm` hier nützlich sein:  `a ≠ b ↔ b ≠ a`.

  "
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

/---/
TheoremDoc ne_comm as "ne_comm" in "Logic"
NewTheorem ne_comm
-- NewConcept: Multivariate functions
