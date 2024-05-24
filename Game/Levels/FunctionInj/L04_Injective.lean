import Game.Metadata


World "FunctionInj"
Level 4

Title "Monotone Funktionen"

Introduction
"
A function `f : A → B` between preorders `A` and `B` is strictly monotone
if `a < b` implies `f a < f b`.
"

open Set Function

Statement StrictMono.injective {A B : Type*} [LinearOrder α] [Preorder β] {f : α → β}
    (hf : StrictMono f)  : Injective f := by
  intro a b h
  rcases lt_trichotomy a b with hlt | heq | hgt
  · apply hf at hlt
    rw [h] at hlt
    simp at *
  · assumption
  · -- proof by symmetry (e.g. `wlog` or `swap`)
    apply hf at hgt
    rw [h] at hgt
    simp at *

NewTheorem lt_trichotomy
