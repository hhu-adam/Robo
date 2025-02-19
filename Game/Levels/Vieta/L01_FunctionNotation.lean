import Game.Metadata

World "Vieta"
Level 1

Title "" -- "Anonyme Funktionen"

Introduction "**Vieta:** Kommt, ich zeig euch etwas …

Er gibt dir ein Stück Papier.
"

Statement (f : ℤ → ℕ) (n : ℤ): f n ≥ 0 := by
  Hint"**Du**: Sieht aus, als wäre `f` eine Abbildung von `ℤ` nach `ℕ`.

  **Robo**: Ja, genau.  Und `f n` ist die Notation für $f(n)$.  Aber auf Leansch lässt man
  die Klammern weg.  Wenn du sie setzen möchtest,  musst du unbedingt Leerzeichen
  um die Klammern setzen – so: `f (n)`.

  **Du**: Ok, will ich mir merken.  Aber da die Abbildung hier nur Werte in ℕ annimmt,
  ist ja eigentlich nichts zu zeigen."
  linarith  -- oder simp

Conclusion"
**Du**: Sag mal, war `→` nicht eben noch eine Implikation?

**Robo**: Ja, richtig. Die benuzten hier das gleiche Zeichen für beides."
