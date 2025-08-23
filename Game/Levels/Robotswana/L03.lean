import Game.Levels.Robotswana.L02_EBasis

World "Robotswana"
Level 3

Title "" -- "Richtige Indizes"

Introduction ""

Conclusion "
  **Du**: Jetzt bin ich aber neugierig, wer diese Zettel hier verloren oder weggeworfen hat. Komm, lass uns weitergehen.
"

open Nat Matrix

/---/
TheoremDoc Matrix.E.mul_same as "E.mul_same" in "Matrix"

-- @[inherit_doc Matrix.single_mul_single_same]
Statement Matrix.E.mul_same {n : ℕ} (i j k : Fin n) : E i j * E j k = E i k  := by
  Hint "**Du**:  Sieht auch richtig aus."
  unfold E
  simp

TheoremTab "Matrix"
