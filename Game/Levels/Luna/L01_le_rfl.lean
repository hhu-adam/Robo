import Game.Metadata


open Nat

World "Luna"
Level 1

Title ""

Introduction
"
Du fühlst dich ein wenig überfahren, aber versuchst trotzdem, ein Gespräch zu beginnen.

**Du**: Ist gut, wir bemühen uns, nichts durcheinander zu bringen. Ist es sehr schwer,
hier Ordnung zu halten?

**Lina**: Man muss zum Beispiel wissen, dass `n ≤ n` ist.
"

Statement (n : ℕ) : n ≤ n := by
  Hint "**Robo**: `rfl`?"
  rfl

Conclusion "
  **Lina**:  Zugegeben, das war ein triviales Beispiel.
"


/---/
TheoremDoc not_le as "not_le" in "≤"
NewTheorem not_le
-- wird später in Vieta einmal erwähnt, aber nirgends gebraucht
