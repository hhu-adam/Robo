import Game.Metadata


World "Quotient"
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

attribute [local instance] Sym2.Rel.setoid

Statement (f : Sym2 A → B) :
    ∀ a₁ a₂, (f ∘ Quotient.mk') (a₁ , a₂) = (f ∘ Quotient.mk') (a₂ , a₁) := by
  intro a₁ a₂
  dsimp
  Branch
    apply congr_arg f
  congr 1
  apply Quotient.sound
  apply Sym2.Rel.swap


-- Statement (f : Sym2 A → B) :
--     let g : A × A → B := fun (a₁ , a₂) ↦  f ⟦ (a₁, a₂) ⟧
--     ∀ a₁ a₂, g (a₁ , a₂) = g (a₂ , a₁) := by
--   intro a₁ a₂
--   simp [g]
--   Branch
--     apply congr_arg f
--   congr 1
--   apply Quotient.sound
--   apply Sym2.Rel.swap
