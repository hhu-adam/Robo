import Game.Metadata

World "Quantus"
Level 2

Title "Natürliche Zahlen"

Introduction ""

Statement (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  Hint "**Du**: Und jetzt Schulmathematik? Man rechnet das einfach aus,
    indem man die Terme umsortiert.

    **Robo**: Wenn die Gleichung stimmt, kannst du auf Leansch sogar einfach
    mit `ring` beweisen, dass das so ist.

    **Du**: Aber `ℕ` ist doch gar kein Ring?

    **Robo**: `ring` funktioniert sogar für sogenannte Halbringe. Ich glaube,
    man sagt `ring`, weil es in (kommutativen) Ringen am besten funktioniert."
  ring

Conclusion ""

NewTactic ring
