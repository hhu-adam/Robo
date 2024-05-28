import Game.Metadata
import Game.Levels.SymmSquare.L02_Sym2

World "Symmetric Square"
Level 7

Title "Classifying Symmetric Functions"

Introduction
"

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

Statement Sym2.liftEquiv {A B : Type*} :
    (Sym2 A → B) ≃ { f : A → A → B | ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁ } := by
  --refine' { .. }
  fconstructor
  · intro f
    --refine' { .. }
    fconstructor
    · exact fun a₁ a₂ => f (⟦ (a₁, a₂) ⟧)
    · intro a₁ a₂
      Branch
        dsimp
        congr 1
        apply Quotient.sound
        apply Sym2.Rel.swap
      apply congr_arg f
      apply Quotient.sound
      apply Sym2.Rel.swap
  · intro f
    exact Quotient.lift (uncurry f.1) <| by
      intro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
      simp [uncurry]
      --simp [Sym2.pair_rel_iff] at h
      cases h
      · rfl
      · exact f.2 x₁ x₂
  · dsimp [LeftInverse]
    intro f
    ext q
    Hint "
      Use `Quotient.exists_rep` to obtain a representative `p` of `q`.
    "
    obtain ⟨p, hp⟩ := Quotient.exists_rep q
    rw [← hp]
    simp [uncurry]
  · dsimp [Function.RightInverse]
    dsimp [LeftInverse]
    intro f
    simp only [Subtype.coe_eta]


NewTheorem Quotient.exists_rep
TheoremTab "Quotient"
