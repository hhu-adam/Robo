import Game.Metadata
import Game.Levels.Quotient.L13_KernelRespect


World "Quotient"
Level 17

Title "Fixed points"

Introduction
"
In this level you show that for an idempotent function `f : A -> A`, the types `A/(ker f)` and `fixedPoints f` are in bijection.
"

open Set Function Setoid


Statement (f : A → A) (h : f ∘ f = f) : Quotient (ker f) ≃ fixedPoints f := by
  trans -- apply Equiv.trans
  exact Equiv.ofBijective (Quotient.lift (rangeFactorization f) respects_ker_rel) (bijective_quotient_lift_range_fac f)
  rw [range_fixedPoints]
  assumption
