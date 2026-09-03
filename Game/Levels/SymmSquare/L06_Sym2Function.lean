import Game.Metadata

World "Symmetric Square"
Level 6

Introduction "Intro Symm L06"

open List Sym

Statement {A B : Type*} (f : Sym2 A → B) :
    let s := Sym2.Rel.setoid A
    ∀ a₁ a₂, (f ∘ Quotient.mk s) (a₁ , a₂) = (f ∘ Quotient.mk s) (a₂ , a₁) := by
  Hint "[Hint sy6sym] A function of two variables is *symmetric* if swapping its arguments
    changes nothing — like `f x y = |x - y|`. Anything defined on unordered pairs is symmetric
    for free: precomposing `f` with the quotient map cannot see the order, because `(a₁, a₂)`
    and `(a₂, a₁)` have the same class."
  intro a₁ a₂
  simp
  Branch
    congr 1
    apply Quotient.sound
    apply Sym2.Rel.swap
  apply congr_arg f
  apply Quotient.sound
  apply Sym2.Rel.swap

NewDefinition Setoid Quotient.mk
