import Game.Metadata
import Game.Levels.Prado.L08_exists_prime_and_dvd

namespace Nat

World "Prado"
Level 9

Title "" -- "Eins"

Introduction "
**Guino:** Ich habe aber tatsächlich eine kleine Aufgabe für euch."

/---/
TheoremDoc Nat.not_prime_one as "not_prime_one" in "ℕ"

Statement not_prime_one : ¬ Nat.Prime 1 := by
  Hint (hidden := true) "**Robo**:  Nicht zu kompliziert denken!
  Erinner dich, wie du gezeigt hattest, dass `2` prim ist!"
  decide

TheoremTab "ℕ"

Conclusion "**Guino**:  Sehr schön.  Nun lasst uns aber weitergehen.
Schaut mal, ist das nicht eine herrlich Treppe?  Lasst uns mal nach oben gehen.
"
