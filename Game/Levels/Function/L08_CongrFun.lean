import Game.Metadata


World "Function"
Level 8

Title "congr_fun"


Introduction
"
**Robo**: Was auch vorkommen kann, ist dass man eine Annahme `h : f = g` hat, und diese
gerne zu `h : ∀ x, f x = g x` umwandeln möchte. Das macht man mit `apply congr_fun at h`.

**Du**: Sag mal, wenn `h : f = g`, dann kann ich doch einfach `rw [h]` brauchen?

**Robo**: Na gut, in so einem einfachen Beispiel ja. Wenn aber `f` ein komplizierterer
Ausdruck ist und noch nicht exact so im Goal steht, dann nicht direkt. Komm, mach's mal
ohne `rw` oder `simp`!
"

open Function

Statement (f g : ℤ → ℤ) (h : f = g) (x : ℤ) : f x = g x := by
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
