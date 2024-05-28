import Game.Metadata


World "Symmetric Square"
Level 3

Title "Equal Unordered Pairs"

Introduction
"

For a setoid `s` on a type `A`, the quotient type `Quotient s` is the type of elements of `A` modulo `s.Rel`.
There is a function `Quotient.mk : A → Quotient s` which maps an element `a : A` to ``⟦a⟧`, a typical element of `Quotient s`.
If elements `a b : A` are congruent, then `⟦a⟧ = ⟦b⟧`. This fact is witnessed by `Quotient.sound`.

"

open Sym2

attribute [local instance] Sym2.Rel.setoid

/-- (1, -2) and (-2, 1) are equal as unordered pairs of integers. -/
Statement : (⟦ (1, -2) ⟧ : Sym2 ℤ) = ⟦ (-2, 1) ⟧ := by
  Branch
    simp [Quotient.eq]
    apply Sym2.Rel.swap
  apply Quotient.sound
  apply Sym2.Rel.swap


NewTheorem Quotient.sound Quotient.eq
TheoremTab "Quotient"
