import Game.Metadata
import Game.Metadata.StructInstWithHoles

World "Cantor"
Level 3

Title "Neg fixed points"

Introduction
"
For an endofunction `f : α → α` the set of fixed points of `f` is defined as follows:

```
def fixedPoints (f : α → α) : Set α :=
  { x : α | IsFixedPt f x }
```
In this level you will prove that an odd function ℝ → ℝ has exactly one fixed point.

"

open Function Set Setoid

Statement : fixedPoints (fun (x : ℝ) => -x) = {0} := by
  ext
  constructor
  · intro h
    apply mem_fixedPoints_iff.mp at h
    simp only [neg_eq_self_iff] at h
    Branch
      simpa [mem_singleton_iff] using h
    tauto
  · intro h
    simp only [mem_singleton_iff] at h
    rw [h]
    apply mem_fixedPoints_iff.mpr
    simp only [neg_zero]
