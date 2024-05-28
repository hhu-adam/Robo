import Game.Metadata
import Game.Levels.Quotient.L13_KernelRespect

World "Quotient"
Level 18

Title "Factorization"

Introduction
"
Any function `f : A → B` can be factored into three functions as `f = m ∘ i ∘ q` where `q` is
a surjection, `i` is a bijection, and `m` is an injection.
"

open Set Function Setoid

#check Function.comp

Statement (A : Type) (B : Type) (f : A -> B) :
    ∃ (C : Type) (D : Type) (q : A -> C) (i : C -> D) (m : D -> B),
    f = m ∘ i ∘ q ∧ Surjective q ∧ Bijective i ∧ Injective m := by
  use (Quotient (α := A) (ker f))
  use (range f)
  use (Quotient.mk (ker f))
  use (Quotient.lift (rangeFactorization f) respects_ker_rel)
  use Subtype.val
  Branch
    fconstructor
    · rfl
    · exact surjective_quotient_mk_ker f
    · exact bijective_quotient_lift_range_fac f
    · exact Subtype.val_injective
  simp
  constructor
  · apply surjective_quotient_mk_ker
  · constructor
    · apply bijective_quotient_lift_range_fac
    · apply Subtype.val_injective
