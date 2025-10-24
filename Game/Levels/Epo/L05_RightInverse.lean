import Game.Metadata

World "Epo"
Level 5

Title ""


/- Introduction "" -/
Introduction "Intro Epo L05"

open Function

Statement :
    let f : ℤ × ℤ → ℤ × ℤ := fun (m, n) ↦ (m + n, m + 2 * n)
    HasRightInverse f := by
  /-
  Hint "
  **Du**:  Hier soll ich vermutlich zeigen, dass ein Rechtsinverses zu `f` existiert?

  **Robo**:  Ja.  Du kannst also zunächst wieder mit `let g : ℤ × ℤ → ℤ × ℤ := fun (m, n) ↦ …` eine Abbildung angeben,
  und sie dann mit `use g` verwenden.

  **Du**:  Gut.  Dann überlege ich also einmal, wie ein Rechtsinverses zu `f` aussehen könnte …"
  -/
  Hint "Try `let g : ℤ × ℤ → ℤ × ℤ := fun (m, n) ↦ …`, `use g`"
  let g : ℤ × ℤ → ℤ × ℤ := fun (m, n) ↦ (2 * m - n, n - m)
  use g
  intro m
  simp [g, f]
  ring

NewDefinition Function.HasRightInverse
