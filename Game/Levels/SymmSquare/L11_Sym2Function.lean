import Game.Metadata
import Game.Levels.SymmSquare.L10
import Game.Levels.SymmSquare.L08
import Game.Levels.SymmSquare.L05_QuotientExistsRep

World "Symmetric Square"
Level 11

Introduction
"Intro Symmm L07:

A function `f : A → B` respects the congruence `r` on `A` if `f x = f y`, for every `r`-congruent
elements `x y : A`.

The universal property of `Quotient r` states that if a function `f : A → B` respects the
congruence `r` then `f` uniquely lifts to a function `Quotient.lift f : Quotient r → B`
defined on a typical element `⟦a⟧` as follows:

```
Quotient.lift f ⟦a⟧ = f a
```

In this level, you show that `Sym2` classifies the symmetric functions in two arguments, that is
there is 1-1 correspondence between the functions `Sym2 A → B` and the functions `A → A → B` that
are symmetric in their arguments.

"

open Function Sym

attribute [local instance] Sym2.Rel.setoid

noncomputable section

Statement Sym2.liftEquiv {A B : Type*} :
    (Sym2 A → B) ≃ { f : A → A → B | ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁ } := by
  refine' { toFun f := ⟨Sym_f f, Sym_f_swap f⟩, invFun g := Sym_g g, left_inv := _, right_inv := _}
  · simp [LeftInverse]
    intro f
    ext q
    obtain ⟨p, hp⟩ := Quotient.exists_rep q
    rw [← hp]
    rfl
  · simp [RightInverse, LeftInverse]
    intro f
    rfl

TheoremTab "Quotient"
