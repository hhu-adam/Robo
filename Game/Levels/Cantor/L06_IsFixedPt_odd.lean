import Game.Metadata
import Game.Levels.Cantor.L05_IsFixedPt_not

World "Cantor"
Level 6

Title ""

Introduction ""

Conclusion "
  Cantor sagt wieder etwas, aber ihr seid zu sehr mit den Aufgaben beschäftigt.
  Ihr bemerkt noch nicht einmal, dass er inzwischen angefangen hat,
  mit dem Einrad zu fliegen.
"

open Function Set

Statement {f : ℝ → ℝ} (h_odd : ∀ x, f (-x) = - f x) (x : ℝ) :
    IsFixedPt f x ↔ IsFixedPt f (- x) := by
  Hint "
    **Du**:  So etwas ähnliches habe ich schon einmal gesehen
    – die Annahme sagt, dass `f` eine „ungerade Funktion ist“.

    **Robo**: Dann mal los.  Ich denke, du wirst hier nichts brauchen,
    was wir nicht schon gesehen haben.
    "
  constructor
  · intro h
    unfold IsFixedPt
    rw [h_odd x]
    rw [h]
  · intro h
    unfold IsFixedPt at h
    rw [h_odd x] at h
    simp at h
    --rw [neg_inj] at h
    assumption

-- /---/
-- TheoremDoc neg_inj as "neg_inj" in "Function"
--
-- NewTheorem neg_inj
-- TheoremTab "Function"
