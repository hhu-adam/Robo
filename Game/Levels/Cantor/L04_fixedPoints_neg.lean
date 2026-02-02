import Game.Metadata
import Game.Levels.Cantor.L03_IsFixedPt_abs

World "Cantor"
Level 4

Title ""

/-
Introduction
""
-/
Introduction "Intro Cantor L04"
/-
Conclusion "
  **Cantor**:  Weiter so!

  Er hat die Kakteen gegen Spatzen eingetauscht.
"
-/
Conclusion "Conclusion Cantor L04"
open Function Set
open scoped CharZero -- Need this so that `simp` can see `CharZero.neg_eq_self_iff`,
                     -- which has a `scoped simp` attribute.
                     -- An alternative to `CharZero.neg_eq_self_iff` would be
                     -- `neg_eq_self ℝ`, which does not have any `simp` attribute.

Statement :
    fixedPoints (fun (x : ℝ) ↦ -x) = {0} := by
  /-
  Hint (strict := true) "
    **Du**: Hier ist `fixedPoints f` wohl die Menge aller Fixpunkte?

    **Robo**: Probiers aus – `unfold` sollte wieder helfen.
  "
  -/
  Hint (strict := true) "See if `fixedPoints f` is the set of all fix points by using `unfold`"
  unfold fixedPoints
  /-
  Hint (strict := true)  "
    **Robo**: Sieht gut aus.  Und jetzt am besten gleich noch `unfold IsFixedPt`.
  "
  -/
  Hint (strict := true) "Try again with `unfold IsFixedPt`"
  unfold IsFixedPt
  /-
  Hint (strict := true) (hidden := true) "
    **Robo**: `simp` kann man immer mal probieren.
  "
  -/
  Hint (strict := true) (hidden := true) "Again try `simp`"
  simp  -- uses `CharZero.neg_eq_self_iff` (scoped simp) and `setOf_eq_eq_singleton`
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
