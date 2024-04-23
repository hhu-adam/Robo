import Game.Metadata
import Game.Metadata.StructInstWithHoles

import Game.Levels.Quotient.L04_Respect

World "Quotient"
Level 5

Title "Bijection"

Introduction
"
A function `f : A → B` respects the congruence `r` on `A` if `f x = f y`, for every `r`-congruent
elements `x y : A`.

The universal property of `Quotient r` states that if a function `f : A → B` respects the
congruence `r` then `f` uniquely lifts to a function `Quotient.lift f : Quotient r → B`
defined on a typical element `⟦a⟧` as follows:

```
Quotient.lift f ⟦a⟧ = f a
```

In this level you prove that the quotient lift of `rangeFactorization f` with respect to the
congruence relation `ker f` is a bijection.

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
