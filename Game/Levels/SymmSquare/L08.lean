import Game.Metadata
import Game.Levels.SymmSquare.L07

World "Symmetric Square"
Level 8

Introduction
"Intro Symm L08:
"

open Function Sym Sym2

attribute [local instance] Sym2.Rel.setoid

variable {A B : Type*}

Statement Sym_f_swap (f : Sym2 A → B) : ∀ a b, Sym_f f a b = Sym_f f b a := by
  intro a b
  unfold Sym_f
  apply congr_arg f
  apply Quotient.sound
  apply Sym2.Rel.swap
