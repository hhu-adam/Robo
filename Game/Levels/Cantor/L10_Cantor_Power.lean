import Game.Metadata

World "Cantor"
Level 10

Title "Cantor"

Introduction
"

In this level you give a second proof of Cantor's theorem by proving a contradiction using the set `{ a | a ∉ f a }`.

"

open Set Function

Statement {A : Type*} : ∀ (f : A → Set A), ¬ Surjective f := by
  intro f hf
  let C := { a | a ∉ f a }
  obtain ⟨c, hc⟩ := hf C
  have h : c ∉ f c := by
      intro h₁
      have : c ∉ f c := by
        rwa [hc] at h₁
      contradiction
  suffices (c ∈ f c) by contradiction
  rw [hc]
  exact h
