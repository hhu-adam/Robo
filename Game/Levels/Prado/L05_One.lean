import Game.Metadata
import Game.Levels.Prado.L04_Prime

namespace Nat

World "Prado"
Level 5

Title "Eins"

Introduction "
**Guino:** Ich habe aber tatsächlich eine kleine Aufgabe für euch."

Statement not_prime_one : ¬ Nat.Prime 1 := by
  Hint (hidden := true) "**Robo**:  Nicht zu kompliziert denken!
  Erinner dich, wie du gezeigt hattest, dass `2` prim ist!"
  decide

TheoremTab "Nat"

Conclusion "**Guino**:  Sehr schön.  Nun lasst uns aber weitergehen.
Schaut mal, ist das nicht eine herrlich Treppe?  Lasst uns mal nach oben gehen.
"
