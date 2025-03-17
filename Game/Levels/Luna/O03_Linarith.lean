import Game.Metadata


World "Luna"
Level 3

Title "" -- "Linarith"

Introduction
"
**Ritha**: Und wie wär's hiermit?
"

Statement (n : ℕ) (h : 2 ≤ n) : n ≠ 0 := by
  Hint "**Du**: `simp` geht hier nicht vermutlich nicht …

  **Robo**: Nein, ist ja auch keine Vereinfachung, die du machen willst.

  **Lina**: Hier brauchst Du unser absolutes Powertool!

  **Ritha**: `linarith`"
  linarith

Conclusion "**Du**: Naja, so beeindruckend war das jetzt auch noch nicht."

NewTactic linarith

/---/
TheoremDoc Nat.pos_iff_ne_zero as "pos_iff_ne_zero" in "ℕ"
NewTheorem Nat.pos_iff_ne_zero
TheoremTab "ℕ"
