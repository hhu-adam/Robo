import Game.Levels.Robotswana.L01_SMulEBasis

World "Robotswana"
Level 2

Title "" -- "Falsche Indizes"

/-
Introduction
"
Kurze Zeit später findet ihr zwei sehr ähnlichen Zettel, wieder
vollgekritzelt, fast alles durchgestrichen.
Die erste Zeile aber lässt sich jeweils gerade noch ausmachen.
"
-/
Introduction "`INTRO` Intro Robotswana L02"

/-
Conclusion "
  **Robo**: Ich speichere dieses `E.mul_of_ne` auch mal, wer weiß.

  **Du**: Jetzt bin ich aber neugierig, wer diese Zettel hier verloren oder weggeworfen hat. Komm, lass uns weitergehen.
"
-/
Conclusion "Conclusion Robotswana L02: save result as `E.mul_of_ne`"

open Nat Matrix

/---/
TheoremDoc Matrix.E.mul_of_ne as "E.mul_of_ne" in "Matrix"

-- @[inherit_doc Matrix.single_mul_single_of_ne]
Statement Matrix.E.mul_of_ne {n : ℕ} (i j : Fin n) {k l : Fin n} (h : j ≠ k) : E i j * E k l = 0 := by
  -- Hint "**Du**: Das sieht jetzt aber nach Matrizen-Multiplikation aus.
  -- Müsste so auch stimmen.
  -- "
  Hint "Story: looks like matrix multiplication"
  unfold E
  -- Hint (hidden := true) "**Robo**: Vergiss aber nicht, dass `simp` die Annahme `{h}` explizit braucht!"
  Hint (hidden := true) "Try `simp` with `{h}`"
  simp [h]

TheoremTab "Matrix"
