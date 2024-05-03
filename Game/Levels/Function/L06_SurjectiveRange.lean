import Game.Metadata

World "Function2"
Level 6

Title "Range of Surjection"


Introduction
"
The range of a function is the set of all outputs.

In this level you show that a function is surjective if and only if the range of
the function is equal to the universal subset of the codomain. For `f : A → B`,
the range of `f` is defined as

```
range f : Set B := {b | ∃ a, f a = b}
```

"

open Function Set

#check Set.range_iff_surjective

Statement surjective_iff_range {f : A → B} : Surjective f ↔ range f = univ := by
  Branch
    exact eq_univ_iff_forall.symm
  constructor
  · intro hf
    ext b
    Branch
      tauto
    constructor
    · tauto
    · intro
      apply hf
  · intro h
    intro b
    Branch
      simpa [← h] using mem_univ b

    change b ∈ range f
    rw [h]
    simp

NewDefinition Set.range
NewTactic change
