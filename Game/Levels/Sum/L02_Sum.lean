import Game.Metadata

open Finset

World "Sum"
Level 2

Title "endliche Summe"

Introduction
"
Ihr schaut euch den nächsten Turm an."

open BigOperators

/-- $\sum_{i=0}^{n-1} 2 = n × 2$. -/
Statement (n : ℕ) : ∑ i : Fin n, 2 = 2 * n := by
  simp
  ring
