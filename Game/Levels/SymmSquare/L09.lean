import Game.Metadata

World "Symmetric Square"
Level 9

Introduction "Intro Symm L09"

open Function Sym Sym2

attribute [local instance] Sym2.Rel.setoid

variable {A B : Type*} {f : A → A → B}

Statement (h : ∀ x y, f x y = f y x) :
    ∀ (a b : A × A), a ≈ b → uncurry f a = uncurry f b := by
  Hint "[Hint sy9resp] Now the other direction: a function of two arguments can only descend
    to unordered pairs if it gives equivalent pairs the same value. Symmetry is exactly what is
    needed — of the two rules generating `≈`, `refl` is trivial and `swap` is `h`."
  intro a b hab
  cases hab
  · rfl
  · apply h

NewDefinition Function.uncurry
