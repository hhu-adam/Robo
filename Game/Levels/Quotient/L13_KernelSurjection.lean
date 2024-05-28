import Game.Metadata

World "Quotient"
Level 13

Title "Surjection"

Introduction
"
In this level you show that the function `Quotient.mk : A → A/(ker f)` is surjective.

"

open Function Set Setoid

Statement surjective_quotient_mk_ker (f : A → B) : Surjective (Quotient.mk (ker f)) := by
  intro q
  -- "choose a representative `b`"
  -- obtain ⟨b⟩ := q
  -- change ∃ a, ⟦a⟧ = ⟦b⟧ -- why does this not pp correctly?
  -- rcases q with ⟨b⟩
  --induction q using Quotient.ind with b
  exact Quotient.exists_rep q


-- example (A : Type) (s: Setoid A) : Surjective (Quotient.mk s) := by
--   intro q
--   exact Quotient.exists_rep q



NewTheorem surjective_quotient_mk_ker
TheoremTab "Quotient"
