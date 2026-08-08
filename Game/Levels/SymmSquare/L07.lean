import Game.Metadata

World "Symmetric Square"
Level 7

Introduction
"Intro Symm L07:
TODO
"

open Function Sym Sym2 List

attribute [local instance] Sym2.Rel.setoid

variable {A B : Type*} {f : Sym2 A → B} {s : Setoid (A × A)} {a b : A}

Statement Sym_f {A B : Type*} : (Sym2 A → B) → (A → A → B) := by
  let s := Sym2.Rel.setoid A
  intro f
  Hint "[] `Function.curry` takes a function of type `α × β → γ` to `α → β → γ`
    in a natural way."
  apply curry (f ∘ Quotient.mk s)
