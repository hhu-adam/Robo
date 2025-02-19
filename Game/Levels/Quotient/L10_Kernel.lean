import Game.Metadata
import Mathlib.GroupTheory.Subgroup.Basic

World "Quotient"
Level 10

Title "" -- "Kernel relation"

Introduction
"
We show that every function `f : A → B` induces a congruence on `A`.
We say elements `x` and `y` of `A` are kernel-congruent if `f x = f y`.
This is the equivalence relation `ker f` on `A` denoted by `ker f`.
```
x ≈ y ↔ f x = f y
```

In this level, you show that if `f : A → B` is injective then
`x` and `y` are kernel-congruent if and only if they are equal.
"

open Function Set Setoid

Statement {A B : Type*} {f : A → B} (finj : Injective f) :
    ∀ x y : A, (ker f).Rel x y ↔ x = y := by
  intro x y
  constructor
  · intro h
    Hint (hidden := true) "
     Recall that x ≈ y ↔ f x = f y
    "
    have : f x = f y := by exact h
    apply finj
    assumption
  · intro h
    rw [h]
