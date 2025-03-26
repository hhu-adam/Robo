import Game.Metadata

World "Saturn"
Level 1

Title ""

Introduction "Plötzlich erreicht euch ein Funkspruch."

namespace MvPolynomial

Statement (x y : ℚ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  Hint "**Du**: Sind wir hier bei den anonymen Schulmathematikern?
  Man rechnet das doch einfach aus, indem man die Terme umsortiert.
  Was sollen wir da zurückfunken?

  **Robo**: Am einfachsten kannst du so eine Gleichung auf Leansch mit `ring` beweisen.
  "
  ring

Conclusion "
  Es kommt ein 👍 zurück.

  **Robo**:  Übrigens heißt dieses Resultat auf Leansch …

  **Du**: Warte, lass mich raten –  `binomi`?

  **Robo**:  Nein.  Das heißt `add_pow_two`.
  Weil in der Formel zuerst ein “+” und dann ein “^2” steht.
"

NewTactic ring

/---/
TheoremDoc add_pow_two as "add_pow_two" in "+ *"

NewTheorem add_pow_two
DisabledTheorem add_pow_two
