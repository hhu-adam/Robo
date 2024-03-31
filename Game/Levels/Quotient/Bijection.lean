import Game.Metadata
import Game.Metadata.StructInstWithHoles

import Game.Levels.Quotient.Respect

World "Quotient"
Level 5

Title "Quotient"

Introduction
"
The crucial universal property of `Quotient r` is the following statement:
If `f : A → B` is any function that respects the congruence `r` in the sense that
for every `x y : A`, `r x y` implies `f x = f y`, then `f` uniquely lifts to a function `Quotient.lift f : Quotient r → B`
defined on a typical element `⟦a⟧` by
```
Quotient.lift f ⟦a⟧ = f a
```

In this level you prove that the quotient lift of `rangeFactorization f` with respect to the
congruence relation `ker f` is a bijection.

Given a map `f : A → B`, the theorem `ker_lift_injective` says that the canonical map from the quotient of `A` by the congruence `ker f` to `B` is injective.

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

-- Remark: another way to prove the injectivity and surjectivity of the quotient lift is to use the cancellation properties. This would still use `ker_lift_injective`
