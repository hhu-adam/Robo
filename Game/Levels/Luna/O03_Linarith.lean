import Game.Metadata


World "Luna"
Level 3

Title "" -- "Linarith"

/-
Introduction
"
**Ritha**: Und wie wär's hiermit?
"
-/
Introduction "Intro Luna O03"

Statement (n : ℕ) (h : 2 ≤ n) : n ≠ 0 := by
  /-
  Hint "**Du**: `simp` geht hier nicht vermutlich nicht …

  **Robo**: Nein, ist ja auch keine Vereinfachung, die du machen willst.

  **Lina**: Hier brauchst Du unser absolutes Powertool!

  **Ritha**: `linarith`"
  -/
  Hint "Try `linarith`"
  linarith

-- Conclusion "**Du**: Naja, so beeindruckend war das jetzt auch noch nicht."
Conclusion "Conclusion Luna O03"

NewTactic linarith

/---/
TheoremDoc Nat.pos_iff_ne_zero as "pos_iff_ne_zero" in "ℕ"
NewTheorem Nat.pos_iff_ne_zero
TheoremTab "ℕ"
