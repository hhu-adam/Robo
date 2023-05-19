gimport Game.Metadata

import Game.ToBePorted
import Game.Options.MathlibPart

import Game.Levels.Sum.L03_ArithSum

World "Sum"
Level 4

Title "Summe aller ungeraden Zahlen"

Introduction
"
Aus reiner Neugierde gehst Du zu einem etwas kleineren Nachbarsturm hinüber.
"
set_option tactic.hygienic false

open Fin

open BigOperators

Statement
    "$\\sum_{i = 0}^n (2n + 1) = n ^ 2$."
    (n : ℕ) : (∑ i : Fin n, (2 * (i : ℕ) + 1)) = n ^ 2 := by
  Hint "**Robo**: Da steht nichts neues, oder? Viel Glück."
  induction n
  simp
  Hint (hidden := true) "Den Induktionschritt bei Summen solltest du wie gesagt
  immer mit `rw [sum_univ_castSucc]` beginnen."
  rw [sum_univ_castSucc]
  simp
  rw [n_ih]
  --rw [Nat.succ_eq_add_one]
  ring

LemmaTab "Sum"
