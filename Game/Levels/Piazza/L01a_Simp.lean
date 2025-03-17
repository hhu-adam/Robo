
import Game.Metadata

World "Piazza"
Level 1

Title ""

Introduction
"
**Mem**:  Wie wärs denn hiermit?
"

open Set

Statement : 9 ∈ {n : ℕ | Odd n} := by
  Hint "
    **Robo**:  Ich glaube, am einfachsten kommst du hier mit `simp` weiter.
  "
  simp
  Hint (hidden := true) "
    **Robo**:  Erinner dich an `decide`.
  "
  decide

TheoremTab "Set"

NewTactic simp

NewDefinition setOf

Conclusion ""
