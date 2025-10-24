import Game.Metadata

World "Prado"
Level 1

Title ""

/-
Introduction"**Robo**:  Ja, ja.  Wissen wir.

Er formuliert die Aussage schnell in Leansch und hält sie dir hin.
"
-/
Introduction "`INTRO` Intro Prado L01"

/---/
TheoremDoc Nat.prime_two as "prime_two" in "ℕ"

namespace Nat

Statement prime_two : Prime 2 := by
  -- Hint "**Robo** *(flüsternd)*:  Das ist ganz einfach.  Weil `2` eine konkrete Zahl ist
  -- und es einen Algorithmus gibt, um zu entscheiden, ob eine Zahl prim ist, kannst du einfach `decide` verwenden!"
  Hint "Try `decide`"
  decide

TheoremTab "ℕ"

/-
Conclusion "
**Du**:  In der Tat.  Wissen wir.  Und was gibt es noch für Exponate?

Guino  wird etwas verlegen.

**Guino**:  Nun, wie gesagt, wir haben gerade erst geöffnet.
Und wir hatten uns entschieden, zunächst nur die allerschönsten Primzahlen auszustellen:
die geraden. Momentan ist die `2` unser einziges Exponat.
Aber wir arbeiten mit Hochdruck daran, weitere gerade Primzahlen für unsere Dauerausstellung zu finden."
-/
Conclusion "Conclusion Prado L01: Present `2` as prime number"

NewDefinition Nat.Prime
