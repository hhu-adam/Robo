import Game.Metadata


World "Symmetric Square"
Level 1

Title "Symmetric square relation is transitive"

Introduction
"

An unordered pair is a collection of two elements that are not ordered.
For example, the unordered pair `{1,2}` is the same as the unordered pair `{2, 1}`.
In other words, the order of the elements in an unordered pair does not matter.

For a type `A` the equivalence relation `Sym2.Rel A` consists of two rules:
1. `refl x y` which says `(x,y) ∼ (x,y)` for all `x` and `y` in `A`
2. `sym x y` which says `(x,y) ∼ (y,x)` for all `x` and `y` in `A`

In this level you show that the relation defined by these rules is transitive.

"

open Sym2

Statement Sym2.Rel.trans {x y z : A × A} :
    let r := Sym2.Rel A
    r x y → r y z → r x z := by
  intro h₁ h₂
  cases h₁
  · cases h₂
    · rfl
    · apply Sym2.Rel.swap
  · cases h₂
    · apply Sym2.Rel.swap
    · rfl



NewTheorem Sym2.Rel.trans
TheoremTab "Quotient"
