import Game.Metadata


World "Symmetric Square"
Level 5

Title "Symmetric Function"

Introduction
"

A symmetric function of two variables is a function that is invariant under permutation
of its arguments. For example, the function `f x y = | x - y |` is symmetric, because
`| x - y |  = | y - x |`.

Given a funtion `f : Sym A 2 → B` one can show that the function `f ∘ Quotient.mk' : A × A → B`
is a symmetric functions on `A × A`.

`Quotient.mk'` is a variant of the `Quotient.mk` function that synthesizes the setoid by
typeclass inference. Other than this it works the same way as `Quotient.mk`.

"

open List Sym

Statement (f : Sym2 A → B) :
    let s := Sym2.Rel.setoid A
    ∀ a₁ a₂, (f ∘ Quotient.mk s) (a₁ , a₂) = (f ∘ Quotient.mk s) (a₂ , a₁) := by
  intro a₁ a₂
  dsimp
  Branch
    congr 1
    apply Quotient.sound
    apply Sym2.Rel.swap
  apply congr_arg f
  apply Quotient.sound
  apply Sym2.Rel.swap
