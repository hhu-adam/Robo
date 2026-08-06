import Game.Metadata

World "Symmetric Square"
Level 9

Introduction
"Intro Symm L09:
TODO
"

open Function Sym Sym2

attribute [local instance] Sym2.Rel.setoid

variable {A B : Type*} {f : A → A → B}

Statement Sym_uc (h : ∀ x y, f x y = f y x) :
    ∀ (a b : A × A), a ≈ b → uncurry f a = uncurry f b := by
  intro a b hab
  cases hab
  · rfl
  · apply h
