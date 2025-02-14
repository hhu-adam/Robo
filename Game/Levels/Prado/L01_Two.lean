import Game.Metadata


namespace Nat

World "Prado"
Level 1

Title "Zwei"

Introduction"**Robo**:  Ja, ja.  Wissen wir.

Er formuliert die Aussage schnell in Leansch und hält sie dir hin.
"
Statement prime_two : Prime 2 := by
  Hint "**Robo** *(flüsternd)*:  Das ist ganz einfach.  Weil `2` eine konkrete Zahl ist
  und es einen Algorithmus gibt, um zu entscheiden, ob eine Zahl prim ist, kannst du einfach `decide` verwenden!"
  decide

TheoremTab "Nat"

Conclusion "
**Du**:  In der Tat.  Wissen wir.  Und was gibt es noch für Exponate?

Guino  wird etwas verlegen.

**Guino**:  Nun, wie gesagt, wir haben gerade erst geöffnet.
Und wir hatten uns entschieden, zunächst nur die allerschönsten Primzahlen auszustellen:
die geraden. Momentan ist die `2` unser einziges Exponat.
Aber wir arbeiten mit Hochdruck daran, weitere gerade Primzahlen für unsere Dauerausstellung zu finden."

NewDefinition Prime
