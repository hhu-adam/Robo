import Game.Metadata

World "Quotient"
Level 14

Title "Respect"

Introduction
"
The image of a subset `S` of `A` along a function `f : A → B` is the set of
all elements `b : B` such that there exists an element `a ∈ S` with `f a = b`.
In Lean, the image `S` along `f` is defined by `Set.image f S`, and denoted by `f '' S`.

The range of a function `f : A → B` is the image of the largest subset of `A`, that is `A` itself`,
along `f`. In Lean the range of `f` is defined by `Set.range f`. Note that
`range f` can be promoted to a subtype of `B` with an injection `Subtype.val : range f → B`.
The injectivity is witnessed by `val_injective`.

`rangeFactorization f` lands in the range of `f` and is defined by

```
rangeFactorization f x = ⟨f x, mem_range_self x⟩
```

In this level you show that `rangeFactorization f` respects the congruence `ker f` on `A`.

"

open Function Set Setoid

Statement respects_ker_rel {f : A → B} :
    ∀ (x y : A), (ker f).Rel x y → rangeFactorization f x = rangeFactorization f y := by
  intro x y h
  ext
  simp only [rangeFactorization_coe]
  exact h

NewTheorem respects_ker_rel
TheoremTab "Quotient"
