import Game.Metadata
import Game.Metadata.StructInstWithHoles

World "Cantor"
Level 4

Title "Cantor"

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
    apply mem_fixedPoints_iff.mpr
    rw [h_odd x]
    rw [h]
  · intro h
    apply mem_fixedPoints_iff.mpr
    rw [mem_fixedPoints_iff] at h
    rw [h_odd x] at h
    apply neg_inj.mp h
