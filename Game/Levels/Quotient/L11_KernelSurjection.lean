import Game.Metadata

World "Quotient"
Level 11

Title "Surjection"

Introduction
"
In this level you show that the function `Quotient.mk : A → A/(ker f)` is surjective.

"

open Function Set Setoid

Statement surj_quotient_mk_ker (f : A → B) : Surjective (Quotient.mk <| ker <| f) := by
  intro q
  -- "choose a representative `b`"
  obtain ⟨b⟩ := q
  -- change ∃ a, ⟦a⟧ = ⟦b⟧ -- why does this not pp correctly?
  -- rcases q with ⟨b⟩
  --induction q using Quotient.ind with b
  use b
  rfl

NewTheorem surj_quotient_mk_ker
TheoremTab "Quotient"
