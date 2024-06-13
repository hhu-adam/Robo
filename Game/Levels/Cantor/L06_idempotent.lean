import Game.Metadata
import Game.Levels.Cantor.L05_IsFixedPt_odd

World "Cantor"
Level 7

Title "Idempotent"

Introduction "
**Cantor**: Also noch ein letztes Rätsel, dann kommen wir gleich zurück zum
Diagonalargument.

**Robo**: Oh das sieht anspruchsvoller aus.
"

open Function Set

Statement range_fixedPoints (f : A → A) (h : f ∘ f = f) : range f = fixedPoints f := by
  Hint "**Du**: Etwas womit ich unsicher bin, wie spielt da wohl `{f} ∘ {f} = {f}` mit rein?

  **Robo**: Vermutlich willst du das irgendwann auf ein bestimmtes `x` anwenden.

  Dafür kannst du irgendwann `apply congr_fun at {h}` brauchen, damit
  du `∀ x, ({f} ∘ {f}) x = {f} x` kriegst."
  apply congr_fun at h
  Branch
    ext i
    rw [mem_range]
    rw [mem_fixedPoints]
    unfold IsFixedPt
    constructor
    · intro hx
      rcases hx with ⟨y, hy⟩
      rw [← hy]
      simp_rw [comp_apply] at h
      rw [h y]
    · intro hf
      use i
  rw [Subset.antisymm_iff]
  constructor
  · intro x hx
    rcases hx
    rw [← h_1]
    unfold fixedPoints
    unfold IsFixedPt
    rw [mem_setOf]
    Hint (hidden := true) "**Robo**: Wir hatten einmal `Function.comp_apply`!"
    simp_rw [comp_apply] at h
    rw [h]
  · intro x hx
    simp
    use x
    trivial

TheoremTab "Function"
