import Game.Metadata


World "Vieta"
Level 9

Title "" -- "congr_fun"


Introduction ""

open Function

Statement (f g : ℤ → ℤ) (h : f = g) (x : ℤ) : f x = g x := by
  /-
  Hint "
**Robo**: Und das ist ein Fall für `congr_fun`.
    Hast du `h : f = g` als Annahme, kannst du sie mit mit `apply congr_fun at h` zu `h : ∀ x, f x = g x` umscheiben.

**Du**: Aber könnte ich hier nicht auch einfacher `rw [h]` benutzen?

**Robo**: Ja gut, in diesem einem einfachen Beispiel schon. Wenn aber `f` ein komplizierterer
Ausdruck ist und noch nicht exact so im Beweisziel steht, dann nicht.
Probiers mal, wie ich es gerade gesagt habe.
  "
  -/
  Hint "Try `congr_fun`. Given assumption `h : f = g` rewrite it via `apply congr_fun at h` to `h : ∀ x, f x = g x`.
  `rw [h]` not applicable to more complex `f`"
  apply congr_fun at h
  Branch
    specialize h x
    assumption
  apply h

/---/
TheoremDoc congr_fun as "congr_fun" in "Function"

OnlyTactic apply assumption «have»
NewTheorem congr_fun
TheoremTab "Function"

Conclusion ""
