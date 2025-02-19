import Game.Metadata

World "SetTheory"
Level 4

Title "" -- "Teilmengen"

Introduction
"
Da `A ⊆ B` als `∀ x : ℕ, x ∈ A → x ∈ B` definiert ist,
kannst du auch `intro x` brauchen.
"

open Set

Statement : ({2, 7} : Set ℕ) ⊆ {2, 3, 7, 9} := by
  Branch
    -- TODO: that's unfortunate. Better exercise about `intro`?
    simp
  Branch
    rw [subset_def]
    simp
  intro x
  Hint (hidden := true) "Jetzt zuerst mal nach unserem Schema `simp` benützen,
  um die Aussage auf Logik zu reduzieren."
  simp
  tauto


TheoremTab "Set"

Conclusion ""
