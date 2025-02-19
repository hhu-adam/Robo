import Game.Metadata

import Game.Levels.Quotient.L14_KernelRespect
import Game.Levels.Quotient.L15_KernelInjection


World "Quotient"
Level 16

Title "" -- "Bijection"

Introduction
"
Use the following:
Given a map `f : A → B`, the theorem `ker_lift_injective` says that the canonical
lift map from  `A/ker f → B` is injective.
"

open Function Set Setoid Quotient

Statement bijective_quotient_lift_range_fac (f : A → B) :
    Bijective (Quotient.lift (rangeFactorization f) respects_ker_rel) := by
  constructor
  · intro q q' h
    obtain ⟨a, ha⟩ := Quotient.exists_rep q
    obtain ⟨a', ha'⟩ := Quotient.exists_rep q'
    rw [← ha, ← ha'] at h
    simp [Quotient.lift_mk] at h
    rw [← ha, ← ha']
    simpa [rangeFactorization] using h
  · intro ⟨b, a, h⟩
    use Quotient.mk (ker f) a
    apply Subtype.ext
    exact h

-- Remark: another way to prove the injectivity and surjectivity of the quotient lift is to use
--the cancellation properties. This would use `ker_lift_injective`
-- `ker_lift_injective (rangeFactorization f)`

NewTheorem bijective_quotient_lift_range_fac
TheoremTab "Quotient"
