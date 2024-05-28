import Game.Metadata
import Mathlib.GroupTheory.Subgroup.Basic

World "Quotient"
Level 11

Title "Quotient by kernel of an injection"

Introduction
"
We show that the kernel of an injection is trivial.
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
