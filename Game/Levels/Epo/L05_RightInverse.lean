import Game.Metadata

World "Epo"
Level 5

Title "Does it have a right inverse?"


Introduction
"
Während `Function.RightInverse f g` die konkrete Inverse `g` angibt, ist `HasRightInverse f`
lediglich die Aussage, dass ein Inverses existiert.

Dieses kann natürlich trotzdem mit `let g : ℤ × ℤ → ℤ × ℤ := fun (m, n) ↦ …` definiert werden.
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
