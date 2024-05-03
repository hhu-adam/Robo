import Game.Metadata

World "Quotient"
Level 1

Title "Classes"

Introduction
"
A setoid structure on a type `A` provides a congruence (aka equivalence relation)
`r : A → A → Prop`.
Given a setoind `s` on `A` and the congruence `s.Rel` tells us which elements of `A` are related
to each other by the relation `s.Rel`.

Given a setoid structure `s` on `A` and an element `a : A` the equivalence class of `a`
is the set of all elements of `A` that are congruent to `a`, namely `{x : A | s.Rel x a}`.

In this level you shall prove that the equivalence class of `a` is the same as the equivalence class of `b` iff `a` and `b` are related by the relation `s.Rel`.

"

open Function Set Setoid

/- SH: Hard to believe this is not in mathlib!  -/
/- SH: this is groupoid version of the yoneda lemma for the proposition valued functors.-/
/- SH: Huh... so we can actually apply the Yoneda lemma to prove this? -/
Statement Setoid.rel_iff_eq_classes {s : Setoid A} (a b : A) :
    (s.Rel a b) ↔ { x | s.Rel x a } = { x | s.Rel x b }:= by
  constructor
  · intro hab
    ext x
    constructor
    · intro hax
      dsimp at *
      trans a
      · exact hax
      · exact hab
    · intro hbx
      dsimp at *
      Branch
        exact s.trans (hbx) (s.symm hab)
      trans b
      · exact hbx
      · exact s.symm hab
  · intro h
    have : a ∈ { x | s.Rel x a } := by exact s.refl a
    rw [h] at this
    exact this


NewTheorem Setoid.rel_iff_eq_classes
TheoremTab "Quotient"
