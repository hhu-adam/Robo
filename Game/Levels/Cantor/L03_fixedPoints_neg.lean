import Game.Metadata
import Game.Levels.Cantor.L02_IsFixedPt_abs

World "Cantor"
Level 4

Title "Fixpunkt"

Introduction
"
**Cantor**: Oder schaut hier, die Menge der Fixpunkte von `-(·)` ist ein Singleton.
"

open Function Set Setoid

Statement :
    fixedPoints (fun (x : ℝ) => -x) = {0} := by
  Hint "**Du**: `fixedPoints f` ist dann wohl die Menge aller Fixpunkte?

  **Robo**: Ja, genau: `fixedPoints f := \{ x | IsFixedPt f x }`.

  **Du**: Welche Optionen habe ich nochmals bei Gleichungen von Mengen?

  **Robo** Entweder du brauchst `ext x` um `x ∈ A ↔ x ∈ B` zu zeigen, oder
  du benützt `rw [Subset.antisymm_iff]` um dann `A ⊆ B ∧ B ⊆ A` zu zeigen.
  "
  Branch
    rw [Subset.antisymm_iff]
  ext x
  constructor
  · intro h
    rw [mem_fixedPoints_iff] at h
    simp at h
    Branch
      tauto
    rw [mem_singleton_iff]
    assumption
  · intro h
    rw [mem_singleton_iff] at h
    rw [h]
    rw [mem_fixedPoints_iff]
    simp

/---/
TheoremDoc Function.mem_fixedPoints_iff as "mem_fixedPoints_iff" in "Function"
/---/
DefinitionDoc Function.fixedPoints as "fixedPoints"

NewDefinition Function.fixedPoints
NewTheorem Function.mem_fixedPoints_iff
TheoremTab "Function"
