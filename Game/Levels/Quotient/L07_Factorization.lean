import Game.Metadata
import Game.Metadata.StructInstWithHoles

import Game.Levels.Quotient.L03_Surjection
import Game.Levels.Quotient.L04_Respect
import Game.Levels.Quotient.L05_Bijection

World "Quotient"
Level 7

Title "Quotient"

Introduction
"
Any function `f : A → B` can be factored into three functions as `f = m ∘ i ∘ q` where `q` is
a surjection, `i` is a bijection, and `m` is an injection.
"

open Set Function Setoid

Statement (A : Type u₁) (B : Type u₂) (f : A -> B) :
    ∃ (C : Type u₁) (D : Type u₂) (q : A -> C) (i : C -> D) (m : D -> B),
    f = m ∘ i ∘ q ∧ Surjective q ∧ Bijective i ∧ Injective m := by
  use (Quotient (α := A) (ker f))
  use (range f)
  use (Quotient.mk <| ker <| f)
  use (Quotient.lift (rangeFactorization f) respects_ker_rel)
  use Subtype.val
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · exact surj_quotient_mk_ker f
  · exact bij_quotient_lift_range_fac f
  · exact Subtype.val_injective
