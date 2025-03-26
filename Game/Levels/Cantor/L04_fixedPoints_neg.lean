import Game.Metadata
import Game.Levels.Cantor.L03_IsFixedPt_abs

World "Cantor"
Level 4

Title ""

Introduction
""

Conclusion "
  **Cantor**:  Weiter so!

  Er hat die Kakteen gegen Spatzen eingetauscht.
"
open Function Set

Statement :
    fixedPoints (fun (x : ℝ) ↦ -x) = {0} := by
  Hint (strict := true) "
    **Du**: Hier ist `fixedPoints f` wohl die Menge aller Fixpunkte?

    **Robo**: Probiers aus – `unfold` sollte wieder helfen.
  "
  unfold fixedPoints
  Hint (strict := true)  "
    **Robo**: Sieht gut aus.  Und jetzt am besten gleich noch `unfold IsFixedPt`.
  "
  unfold IsFixedPt
  Hint (strict := true) (hidden := true) "
    **Robo**: `simp` kann man immer mal probieren …
  "
  simp
  /-
  Branch
    rw [Subset.antisymm_iff]
  ext x
  constructor
  · intro h
    simp at h
    assumption
    -- rw [mem_fixedPoints_iff] at h
  · intro h
    simp at h --or: rw [mem_singleton_iff] at h
    rw [h]
    -- rw [mem_fixedPoints_iff]
    simp
-/

NewDefinition Function.fixedPoints
