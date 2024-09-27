import Game.Metadata

World "SetTheory"
Level 10

Title "Teilmengen mit Konditionen"

Introduction
"
Eine wichtige Konstruktion ist noch eine Menge mit Nebenbedingungen:

\"alle natürlichen Zahlen die ungerade sind\".


"

open Set

Statement : 9 ∈ {n : ℕ | Odd n} := by
  Hint "Aber auch hier, `∈ _` gehst du erst einmal mit `simp` an."
  simp
  Hint "Wir hatten bereits einmal wie man aussagen über konkrete Zahlen löst"
  Hint (hidden := true) "das war `decide`."
  decide


/-- -/
DefinitionDoc setOf as "{·|·}"

NewDefinition setOf
TheoremTab "Set"

Conclusion ""
