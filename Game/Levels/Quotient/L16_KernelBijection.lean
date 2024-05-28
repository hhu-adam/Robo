import Game.Metadata

import Game.Levels.Quotient.L14_KernelRespect
import Game.Levels.Quotient.L15_KernelInjection


World "Quotient"
Level 16

Title "Bijection"

Introduction
"
Use the following:
Given a map `f : A → B`, the theorem `ker_lift_injective` says that the canonical
lift map from  `A/ker f → B` is injective.
"

open Function Set Setoid Quotient

section
variable (f : A → B)
#check ker_lift_injective (rangeFactorization f)
end
Statement bijective_quotient_lift_range_fac (f : A → B) :
    Bijective (Quotient.lift (rangeFactorization f) respects_ker_rel) := by
  constructor
  · intro a b h
    apply ker_lift_injective (rangeFactorization f) h
    rcases x with ⟨a⟩
    --obtain ⟨a, ha⟩ := Quotient.exists_rep x
    rcases y with ⟨b⟩
    --obtain ⟨b, hb⟩ := Quotient.exists_rep y
    injections
  · intro ⟨b, a, h⟩
    use Quotient.mk (ker f) a
    apply Subtype.ext
    exact h

-- Remark: another way to prove the injectivity and surjectivity of the quotient lift is to use
--the cancellation properties. This would still use `ker_lift_injective`

NewTheorem bijective_quotient_lift_range_fac
TheoremTab "Quotient"
