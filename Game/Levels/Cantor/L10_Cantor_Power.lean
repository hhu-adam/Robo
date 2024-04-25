import Game.Metadata

World "Cantor"
Level 10

Title "Cantor"

Introduction
"
"

open Set Function

Statement {A : Type*} : ∀ (f : A → Set A), ¬ Surjective f := by
  intro f
  by_contra hf
  let C := { a | a ∉ f a }
  have hsurj := hf C
  rcases hsurj with ⟨y, hy⟩
  unfold_let C at hy
  by_cases y ∈ f y
  · suffices hn : y ∉ f y
    · contradiction
    rw [hy]
    rw [mem_setOf]
    simp
    assumption
  · apply h
    rw [hy]
    rw [mem_setOf]
    assumption
