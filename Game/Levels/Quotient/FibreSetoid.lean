import Game.Metadata
import Game.Metadata.StructInstWithHoles


World "Quotient"
Level 1

Title "Quotient"

Introduction
"
A setoid structure on a type `A` provides a relation `r : A → A → Prop` which is congruence (aka equivalence relation). The congruence `r` tell us which elements of `A` are congruent to other elements of `A`. We show that every function `f : A → B` induces a congruence on `A`, which we call the fibre congruence, and is defined by `x ~ y ↔ f x = f y`.
"

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
