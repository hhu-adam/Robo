import Game.Levels.Robotswana.L01_SMulEBasis

World "Robotswana"
Level 2

Title "" -- "Falsche Indizes"

Introduction "Intro Robotswana L02"

Conclusion "Conclusion Robotswana L02: save result as `E.mul_of_ne`"

open Nat Matrix

/---/
TheoremDoc Matrix.E.mul_of_ne as "E.mul_of_ne" in "Matrix"

-- @[inherit_doc Matrix.single_mul_single_of_ne]
Statement Matrix.E.mul_of_ne {n : ℕ} (i j : Fin n) {k l : Fin n} (h : j ≠ k) : E i j * E k l = 0 := by
  -- Hint "**Du**: Das sieht jetzt aber nach Matrizen-Multiplikation aus.
  -- Müsste so auch stimmen.
  -- "
  Hint "Looks like matrix multiplication"
  unfold E
  -- Hint (hidden := true) "**Robo**: Vergiss aber nicht, dass `simp` die Annahme `{h}` explizit braucht!"
  Hint (hidden := true) "Try `simp` with `{h}`"
  simp [h]

TheoremTab "Matrix"
