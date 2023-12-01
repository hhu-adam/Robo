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

NewTactic linarith
NewLemma Nat.pos_iff_ne_zero
LemmaTab "Nat"

Conclusion "**Du**: Naja, so beeindruckend war das jetzt auch noch nicht."
