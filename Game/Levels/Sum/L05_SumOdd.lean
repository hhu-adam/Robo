import Game.Metadata

import Game.Levels.Sum.L04_ArithSum

World "Sum"
Level 5

open Fin
open BigOperators

Title "Summe aller ungeraden Zahlen"

Introduction
"
Aus reiner Neugierde gehst Du zu einem etwas kleineren Nachbarsturm hinüber.
"

/-- $\sum_{i = 0}^{n-1} (2i + 1) = n ^ 2$. -/
Statement (n : ℕ) : (∑ i : Fin n, (2 * i + 1)) = n ^ 2 := by
  Hint "**Robo**: Das funktioniert genau gleich wie zuvor, viel Glück."
  induction n
  simp
  Hint (hidden := true) "Den Induktionschritt bei Summen solltest du wie gesagt
  immer mit `rw [sum_univ_castSucc]` beginnen."
  rw [sum_univ_castSucc]
  simp
  rw [n_ih]
  --rw [Nat.succ_eq_add_one]
  ring

TheoremTab "Sum"
