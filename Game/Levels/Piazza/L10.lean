import Game.Metadata

World "Piazza"
Level 10

Title ""

/-
Introduction
"
**Mem**:  Lasst mich auch noch einmal eine Frage stellen!
"
-/
Introduction "`INTRO` Intro Piazza L10"

open Set Nat -- Nat is opened in case someone wants to use `Nat.not_odd_iff_even` here

Statement : {2, 7} ⊆ {2} ∪ { n : ℕ | Odd n} := by
  -- Hint (hidden := true) "
  --   **Robo**:  Ich würde wieder mit `intro` anfangen.
  -- "
  Hint (hidden := true) "Start with `intro`"
  intro x
  -- Hint (hidden := true) "
  --  **Robo**:  Und noch ein `intro`!
  -- "
  Hint (hidden := true) "Try `intro` again `SECOND`"
  intro hx
  simp at *
  obtain h | h := hx
  · tauto -- or  left, assumption
  · right
    rw [h]
    decide

TheoremTab "Set"

-- Conclusion "
-- **Mem**:  Ja super, ihr habt aber schnell gelernt!
-- "
Conclusion "`CONC` Conclusion Piazza L10"
