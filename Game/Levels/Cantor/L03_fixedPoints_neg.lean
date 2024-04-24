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
    rw [mem_fixedPoints_iff] at h
    Branch
      simp only [neg_eq_self_iff] at h
    simp at h
    Branch
      tauto
    rw [mem_singleton_iff]
    assumption
  · intro h
    rw [mem_singleton_iff] at h
    rw [h]
    rw [mem_fixedPoints_iff]
    simp

NewDefinition Function.fixedPoints
NewTheorem Function.mem_fixedPoints_iff
TheoremTab "Function"
