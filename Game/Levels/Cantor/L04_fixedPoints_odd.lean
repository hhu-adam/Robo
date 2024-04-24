import Game.Metadata

World "Cantor"
Level 4

Title "Odd fixed points"

Introduction
"
For an endofunction `f : α → α` the set of fixed points of `f` is defined as follows:

```
def fixedPoints (f : α → α) : Set α :=
  { x : α | IsFixedPt f x }
```

In this level you will prove that an the set of fixed points of an odd function is closed under negation.

"

open Function Set Setoid

Statement {f : ℝ → ℝ} (h_odd : ∀ x, f (-x) = - f x) :
    x ∈ fixedPoints f ↔ - x ∈ fixedPoints f := by
  constructor
  · intro h
    rw [mem_fixedPoints_iff]
    rw [h_odd x]
    rw [h]
  · intro h
    rw [mem_fixedPoints_iff] at *
    rw [h_odd x] at h
    rw [neg_inj] at h
    assumption

NewTheorem neg_inj
TheoremTab "Function"
