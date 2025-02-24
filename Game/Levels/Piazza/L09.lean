import Game.Metadata

World "Piazza"
Level 9

Title "" -- "Mengen"

Introduction
"

Das Komplement einer Menge ist `Aᶜ`, was das gleiche ist wie `(univ : Set ℕ) \\ A`.

Aber auch hier: üb das Schema.
"

open Set

Statement (A B C : Set ℕ) :
    (A \ B)ᶜ ∩ (C \ B)ᶜ = ((univ \ A) \ C) ∪ (univ \ Bᶜ) := by
  ext i
  simp
  tauto

/-- -/
DefinitionDoc Set.compl as "·ᶜ"


NewDefinition Set.compl
TheoremTab "Set"

Conclusion ""
