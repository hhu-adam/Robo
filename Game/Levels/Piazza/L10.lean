import Game.Metadata

World "Piazza"
Level 10

Title ""

Introduction
"
**Mem**:  Lasst mich auch noch einmal eine Frage stellen!
"

open Set Nat -- Nat is opened in case someone wants to use `Nat.not_odd_iff_even` here

Statement : {2, 7} ⊆ {2} ∪ { n : ℕ | Odd n} := by
  Hint (hidden := true) "
    **Robo**:  Ich würde wieder mit `intro` anfangen.
  "
  intro x
  Hint (hidden := true) "
    **Robo**:  Und noch ein `intro`!
  "
  intro hx
  simp at *
  obtain h | h := hx
  · tauto -- or  left, assumption
  · right
    rw [h]
    decide

TheoremTab "Set"

Conclusion "
**Mem**:  Ja super, ihr habt aber schnell gelernt!
"
