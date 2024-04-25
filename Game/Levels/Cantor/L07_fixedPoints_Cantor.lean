import Game.Metadata

World "Cantor"
Level 7

Title "Cantor"

Introduction
"
**Cantor**: Genug gerätselt, jetzt aber zum Diagonalargument, Wusstet ihr, dass
keine Funktion `A → Set A` surjektiv sein kann? Denn das würde implizieren,
dass jede Funktion `Prop → Prop` einen Fixpunkt hätte.

Aber zuerst einen Tipp!
"

open Function Set

Statement cantor_diagonal_isFixedPt {f : A → A → Y} (g : A → Y) (s : Y → Y)
    (h₁ : ∀ x, g x = s (f x x)) (a : A) (h₂ : f a = g) : IsFixedPt s (f a a) := by
  unfold IsFixedPt
  have h₃ := h₁ a
  rw [← h₃]
  rw [h₂]
