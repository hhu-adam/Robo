import Game.Metadata

World "Quantus"
Level 5

Title ""

Introduction
"Eine weitere Frage erreicht euch.  Dieses stammt offenbar aus dem anderen Lager."

open Nat

Statement (i : ℕ) (h : Odd i): (-1 : ℤ)^i  + 1 = 0 := by
  Hint "
    **Robo**:  Ich glaube, hier kommst du mit `Odd.neg_pow` weiter.
  "
  rw [Odd.neg_pow]
  ring
  assumption

/---/
TheoremDoc Odd.neg_pow as "Odd.neg_pow" in "ℕ"

/---/
TheoremDoc Even.neg_pow as "Even.neg_pow" in "ℕ"

NewTheorem Odd.neg_pow Even.neg_pow


Conclusion ""
