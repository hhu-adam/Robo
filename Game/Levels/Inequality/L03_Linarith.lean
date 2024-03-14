import Game.Metadata


World "Inequality"
Level 3

Title "Linarith"

Introduction
"
**Ritha**: Und wie wärs hiermit?
"

Statement (n : ℕ) (h : 2 ≤ n) : n ≠ 0 := by
  Hint "**Du**: `simp` geht hier nicht vermutlich nicht …

  **Robo**: Nein, ist ja auch keine Vereinfachung, die du machen willst.

  **Lina**:  Hier brauchst Du unser absolutes Powertool!

  **Ritha**: `linarith`"
  linarith

Conclusion "**Du**: Naja, so beeindruckend war das jetzt auch noch nicht."

/--
`linarith` löst Systeme linearer (Un-)Gleichungen.

## Detail
`linarith` kann lineare Gleichungen und Ungleichungen beweisen indem
es das Gegenteil vom Goal annimmt und versucht einen Widerspruch in den
Annahmen zu erzeugen (Widerspruchsbeweis). Es braucht ein `≤` definiert um
zu funktionieren.

## Beispiel

Folgendes kann `linarith` beweisen.
```
Objekte
  x y : ℤ
  h₁ : 5 * y ≤ 35 - 2 * x
  h₂ : 2 * y ≤ x + 3
Goal
  y ≤ 5
```
-/
TacticDoc linarith

NewTactic linarith
NewTheorem Nat.pos_iff_ne_zero
TheoremTab "Nat"
