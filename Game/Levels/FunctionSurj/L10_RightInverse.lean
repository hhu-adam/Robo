import Game.Metadata

World "FunctionSurj"
Level 10

Title "Does it have a right inverse?"


Introduction
"

We say `f : A → B` has a right inverse if there exists a function `g : B → A` such that `f ∘ g = id`.
"

open Function

Statement :
    let f : ℤ × ℤ → ℤ × ℤ := fun (m, n) ↦ (m + n, m + 2 * n)
    HasRightInverse f := by
  let g : ℤ × ℤ → ℤ × ℤ := fun (m, n) ↦ (2 * m - n, n - m)
  use g
  intro m
  simp [g, f]
  ring

NewDefinition Function.HasRightInverse
