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
example : A × A → B :=
  let s := Sym2.Rel.setoid A
  (f ∘ Quotient.mk s)

example : A → A → B :=
  let s := Sym2.Rel.setoid A
  Function.curry (f ∘ Quotient.mk s)

Statement Sym_f {A B : Type*} : (Sym2 A → B) → (A → A → B) := by
  let s := Sym2.Rel.setoid A
  intro f
  apply curry (f ∘ Quotient.mk s)
