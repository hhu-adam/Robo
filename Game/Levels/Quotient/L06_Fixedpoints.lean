import Game.Metadata
import Game.Metadata.StructInstWithHoles

import Game.Levels.Quotient.L04_Respect
import Game.Levels.Quotient.L05_Bijection

World "Quotient"
Level 6

Title "Quotient"

Introduction
"
In this level you show that for an idempotent function `f : A -> A`, the types `A/(ker f)` and `fixedPoints f` are in bijection.
"

open Set Function Setoid

Statement (f : Function.End A) (h : f ∘ f = f) : Quotient (ker f) ≃ fixedPoints f := by
  apply Equiv.trans
  exact Equiv.ofBijective (Quotient.lift (rangeFactorization f) respects_ker_rel) (bij_quotient_lift_range_fac f)
  refine {?..!}
  sorry
  sorry
  sorry
  sorry
