import Game.Metadata
import Game.Metadata.StructInstWithHoles

import Game.Levels.Quotient.Surjection
import Game.Levels.Quotient.Respect
import Game.Levels.Quotient.Bijection

World "Quotient"
Level 6

Title "Quotient"

Introduction
"
Any function `f : A → B` can be factored into three functions as `f = m ∘ i ∘ q` where `q` is a surjection, `i` is a bijection, and `m` is an injection.
"

open Set Function Setoid

Statement (A : Type u₁) (B : Type u₂) (f : A -> B) :
    ∃ (C : Type u₁) (D : Type u₂) (q : A -> C) (i : C -> D) (m : D -> B), Surjective q ∧ Bijective i ∧ Injective m ∧ f = m ∘ i ∘ q := by
  use (Quotient (α := A) (ker f))
  use (range f)
  use (Quotient.mk <| ker <| f)
  use (Quotient.lift (rangeFactorization f) respects_ker_rel)
  use Subtype.val
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact surj_quotient_mk_ker f
  · exact bij_quotient_lift_range_fac f
  · exact Subtype.val_injective
  · rfl
