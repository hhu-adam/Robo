import Game.Metadata


World "FunctionInj"
Level 4

Title "Monotone Funktionen"

Introduction
"
"

open Set Function

Statement StrictMono.injective {f : ℤ → ℤ}
    (hf : StrictMono f)  : Injective f := by
  intro a b h
  obtain hlt | heq | hgt := lt_trichotomy a b
  · apply hf at hlt
    rw [h] at hlt
    linarith
  · assumption
  · -- proof by symmetry (e.g. `wlog` or `swap`)
    apply hf at hgt
    rw [h] at hgt
    linarith
