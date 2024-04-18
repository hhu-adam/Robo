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

open Set Function Setoid Cardinal

#check range

theorem tmp₀ (f : Function.End A) (h : f ∘ f = f) : range f = fixedPoints f := by
  apply Subset.antisymm
  · intro x hx
    rcases hx
    rw [← h_1]
    unfold fixedPoints
    unfold IsFixedPt
    rw [mem_setOf]
    apply congr_fun at h -- :D
    simp only [comp_apply] at h
    rw [h]
  · intro x hx
    rw [mem_range] -- is simp
    use x
    trivial

Statement (f : Function.End A) (h : f ∘ f = f) : Quotient (ker f) ≃ fixedPoints f := by
  trans -- apply Equiv.trans
  exact Equiv.ofBijective (Quotient.lift (rangeFactorization f) respects_ker_rel) (bij_quotient_lift_range_fac f)
  rw [tmp₀]
  assumption
