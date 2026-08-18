import Game.Metadata

World "Iso"
Level 5

/-
Introduction
"
In this level you show that there every bijection gives rise to an equivalence.
"
-/
Introduction "Intro Iso L05"

noncomputable section

open Function

Statement {A B : Type} (f : A → B) (h : Bijective f) : A ≃ B := by
  Hint "[Hint w6ktp] A map is bijective exactly when it has a two-sided inverse, i.e. some
  `g : B → A` undoing `f` in both directions."
  Hint (hidden := true) "[Hint r2xdn] Remember the theorem `bijective_iff_has_inverse` and rewrite `{h}` with it."
  rw [bijective_iff_has_inverse] at h
  Hint (hidden := true) "[Hint f8vqc] Use `choose` to extract the function from `{h}`; `obtain` cannot, since the goal `A ≃ B` is data rather than a proposition."
  choose g hg using h
  Branch
    constructor
    · apply f
    · apply g
    · apply hg.1
    · apply hg.2
  obtain ⟨hg₁, hg₂⟩ := hg
  constructor
  · apply f
  · apply g
  · apply hg₁
  · apply hg₂
