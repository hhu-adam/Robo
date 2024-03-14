import Game.Metadata

World "Predicate"
Level 1

Title "Natürliche Zahlen"

Introduction "Du schaust dir die erste Seite an."

Statement (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  Hint "**Du**: Das ist doch Schulmathematik! Man rechnet das einfach aus,
    indem man die Terme umsortiert.

    **Robo**: Wenn die Gleichung stimmt, kannst du auf Leansch sogar einfach
    mit `ring` beweisen, dass das so ist.

    **Du**: Aber `ℕ` ist doch gar kein Ring?

    **Robo**: `ring` funktioniert sogar für sogenannte Halbringe. Ich glaube,
    man sagt `ring`, weil es in  (kommutativen) Ringen am besten funktioniert."
  ring

Conclusion ""

/--
Löst Gleichungen mit den Operationen `+, -, *, ^`.

## Details
Insbesondere funktioniert `ring` in Ringen/Semiringen wie z.B. `ℕ, ℤ, ℚ, …`
(i.e. Typen `R` mit Instanzen `Ring R` oder `Semiring R`).
Die Taktik ist besonders auf kommutative Ringe (`CommRing R`) ausgelegt.

## Hilfreiche Resultate

* `ring` kann nicht wirklich mit Division (`/`) oder Inversen (`⁻¹`) umgehen. Dafür ist die
  Taktik `field_simp` gedacht, und die typische Sequenz ist
  ```
  field_simp
  ring
  ```
-/
TacticDoc ring

NewTactic ring
