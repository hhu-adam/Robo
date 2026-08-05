import Game.Metadata

World "Symmetric Square"
Level 10

Introduction
"Intro Symm L10:
"

open Function Sym Sym2

attribute [local instance] Sym2.Rel.setoid

variable {A B : Type*}

Statement Sym_g : {f : A → A → B | ∀ a b, f a b = f b a} → (Sym2 A → B) := by
  intro f
  apply Quotient.lift (uncurry f.1)
  intro a b hab
  cases hab
  · rfl
  apply f.2
