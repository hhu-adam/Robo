import Game.Metadata

World "Function2"
Level 15
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
  obtain hlt | heq | hgt := lt_trichotomy a b
  · apply hf at hlt
    rw [h] at hlt
    exfalso
    exact lt_irrefl (f b) hlt
  · exact heq
  · -- proof by symmetry (e.g. `wlog` or `swap`)
    apply hf at hgt
    rw [h] at hgt
    exfalso
    exact lt_irrefl (f b) hgt
