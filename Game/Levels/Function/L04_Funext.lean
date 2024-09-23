import Game.Metadata


World "Function"
Level 4

Title "funext"


Introduction
"
**Du**: Per Definition sind doch zwei Funktionen gleich, wenn sie angewendet auf
jedes Element den gleichen Wert haben…

**Robo**: Das kannst du mit `funext x` machen, welches, ein beliebiges `x` annimmt, und
das Goal von `f = g` zu `f x = g x` ändert.
"

open Function

Statement :
    let f := fun (x : ℤ) ↦ x ^ 2;
    let g := fun x ↦ f (-x);
    f = g := by
  funext x
  Hint (hidden := true) "**Robo**: Zur erinnerung, `ring` sieht durch lokale Definition."
  ring

OnlyTactic funext ring
NewTactic funext
TheoremTab "Function"

Conclusion ""
