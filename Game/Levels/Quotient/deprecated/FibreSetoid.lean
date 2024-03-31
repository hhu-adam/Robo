import Game.Metadata
import Game.Metadata.StructInstWithHoles


World "Quotient"
Level 0

Title "Quotient"

Introduction
"
A setoid structure on a type `A` provides a relation `r : A → A → Prop` which is congruence (aka equivalence relation). The congruence `r` tell us which elements of `A` are congruent to other elements of `A`.


We show that every function `f : A → B` induces a congruence on `A`: We say elements `x` and `y` of `A` are in the same fibre of `f` if `f x = f y`.
```
x ~ y ↔ f x = f y
```

"

open Function Set Setoid

instance fibre_setoid (f : A → B) : Setoid A where
  r x y := f x = f y
  iseqv := by
    refine {?..!}
    · intro x
      rfl
    · intro x y h
      exact h.symm
    · intro x y z h₁ h₂
      exact h₁.trans h₂
