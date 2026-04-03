import Game.Metadata

World "Saturn"
Level 2

Title "[Saturn.L02] Title"

-- Introduction "Der nächste Funkspruch sieht ein bisschen anders aus."
Introduction "Intro Saturn L02"

namespace MvPolynomial

Statement (x y : ℚ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  /-
  Hint "**Du**: Sind wir hier bei den anonymen Schulmathematikern?
  Man rechnet das doch einfach aus, indem man die Terme umsortiert.
  Was sollen wir da `binomi` zurückfunken?

  **Robo**: Nein, die Gleichung heißt in diesem Universum natürlich `add_pow_two`,
  weil in der Formel zuerst ein “+” und dann ein “^2” steht.
  Du könntest also `rw [add_pow_two]` benutzen.
  Danach sieht die linke Seite exakt wie die rechte aus, und du bist fertig."
  -/
  Hint "Explain misfit of `binomi`. Try `add_pow_two` via `rw [add_pow_two]`"
  Branch
    ring
  rw [add_pow_two]

/-
Conclusion "
  Es kommt ein 👍 zurück.

  **Robo**: Du hättest allerdings auch einfach `ring` sagen können.
  "
-/
Conclusion "Conclusion Saturn L02: `ring` could have been used as well"
NewTactic ring

/-- [Saturn.L02] documentation 1 -/
TheoremDoc add_pow_two as "add_pow_two" in "+ *"

NewTheorem add_pow_two
