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
  rw [bijective_iff_has_inverse] at h
  choose g hg using h
  constructor
  · apply f
  · apply g
  · apply hg.1
  · apply hg.2
