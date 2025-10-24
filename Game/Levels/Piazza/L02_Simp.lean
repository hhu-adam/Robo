
import Game.Metadata

World "Piazza"
Level 2

Title ""

/-
Introduction
"
**Mem**:  Wie wärs denn hiermit?
"
-/
Introduction "`INTRO` Intro Piazza L02"

open Set

Statement : 9 ∈ {n : ℕ | Odd n} := by

  -- Hint "
  --  **Robo**:  Ich glaube, am einfachsten kommst du hier mit `simp` weiter.
  -- "
  Hint "Try `simp`"
  simp
  -- Hint (hidden := true) "
  --  **Robo**:  Erinner dich an `decide`.
  -- "
  Hint (hidden := true) "Try `decide`"
  decide

TheoremTab "Set"

NewTactic simp

NewDefinition setOf

-- Conclusion ""
Conclusion "Conclusion Piazza L02 "
