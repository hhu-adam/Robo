import Game.Metadata


World "Symmetric Square"
Level 2

Title "Permutation Equivalence Relation"

Introduction
"
A setoid structure on a type `A` provides an equivalence relation (aka congruence)
`r : A → A → Prop`.

Given a setoind `s` on `A`, the congruence `s.Rel` tells us which elements of `A` are related
to each other by the relation `s.Rel`. We sometimes write `a ≈ b` if `a` and `b`
are congruent modulo `s.Rel`, that is if `s.Rel a b` holds.

The relation `Sym2.Rel A` on `A × A` is an equivalence relation on `A × A` and as such
it gives `A × A` a setoid structure.

"

open Sym2

attribute [local instance] Sym2.Rel.setoid

/-- Two pairs are related by `Sym2.Rel` if they are permutations of each other. -/
Statement Sym2.pair_rel_iff {x y z w : A} : (x, y) ≈ (z, w) ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  constructor
  · intro h
    cases h
    tauto
    tauto
  · intro h
    cases h
    · rw [h_1.1, h_1.2]
    · rw [h_1.1, h_1.2]
      apply Sym2.Rel.swap


NewTheorem Sym2.rel_iff
TheoremTab "Quotient"
