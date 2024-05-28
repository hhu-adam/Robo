import Game.Metadata
import Mathlib.GroupTheory.Subgroup.Basic

World "Quotient"
Level 12

Title "Kernel"

Introduction
"
We show that every function `f : A → B` induces a congruence on `A`. We say elements `x`
and `y` of `A` are kernel-congruent if `f x = f y`.
This is the equivalence relation `ker f` on `A` denoted by `ker f`.
```
x ≈ y ↔ f x = f y
```

You might be familiar with the kernel of a group homomorphism which the set of elements
that are sent to the identity element of the codomain. The kernel of a group
homomorphism is a subgroup of the domain.

In this level you show that these two notions of kernel coincide: Two elements `x` and `y` of `A` are kernel congruent if and only if their difference is in the kernel of `f`.

"

open Function Set Setoid

Statement {A B : Type*} [AddGroup A] [AddGroup B] {f : A →+ B} {x y : A} :
    (ker f).Rel x y ↔ (x - y) ∈ f.ker := by
  Branch
    -- alternative proof using `AddMonoidHom.mem_ker` from mathlib
    simp_rw [AddMonoidHom.mem_ker f]
    simp only [map_sub]
    simp [ker_def]
    simp [sub_eq_zero]
  constructor
  · intro h
    simp [ker_def] at h
    rw [← sub_eq_zero, ← f.map_sub] at h
    exact h
  · intro h
    simp [ker_def]
    rw [← sub_eq_zero, ← f.map_sub]
    exact h
