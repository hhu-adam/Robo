import Game.Metadata

import Game.Levels.Quotient.L12_KernelRespect

World "Quotient"
Level 13

Title "Bijection"

Introduction
"
Use the following:
Given a map `f : A → B`, the theorem `ker_lift_injective` says that the canonical lift map from
`A/ker f → B` is injective.

"

open Function Set Setoid Quotient

Statement bij_quotient_lift_range_fac (f : A → B) :
    Bijective (Quotient.lift (rangeFactorization f) respects_ker_rel) := by
  constructor
  · intro x y h
    apply ker_lift_injective f
    rcases x with ⟨a⟩
    rcases y with ⟨b⟩
    injections
  · intro ⟨b, a, h⟩
    use Quotient.mk (ker f) a
    apply Subtype.ext
    exact h

-- Remark: another way to prove the injectivity and surjectivity of the quotient lift is to use
--the cancellation properties. This would still use `ker_lift_injective`

NewTheorem bij_quotient_lift_range_fac
TheoremTab "Quotient"
