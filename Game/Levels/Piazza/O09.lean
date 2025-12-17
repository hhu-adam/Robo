import Game.Metadata

World "Piazza"
Level 9

Title "" -- "Mengen"

/-
Introduction
"

Das Komplement einer Menge ist `Aᶜ`, was das gleiche ist wie `(univ : Set ℕ) \\ A`.

Aber auch hier: üb das Schema.
"
-/
Introduction "Intro Piazza O09"

open Set

Statement (A B C : Set ℕ) :
    (A \ B)ᶜ ∩ (C \ B)ᶜ = ((univ \ A) \ C) ∪ (univ \ Bᶜ) := by
  ext i
  simp
  tauto

/-- -/
DefinitionDoc Set.compl as "·ᶜ" in "Set"


NewDefinition Set.compl
TheoremTab "Set"

-- Conclusion ""
Conclusion "Conclusion Piazza O09"
