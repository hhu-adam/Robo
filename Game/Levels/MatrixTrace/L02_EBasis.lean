import Game.Levels.MatrixTrace.L01_SMulEBasis

World "Trace"
Level 2

Title "Falsche Indizes"

Introduction
"
Kurze Zeit später findet ihr zwei sehr ähnlichen Zettel, wieder
vollgekritzelt, fast alles durchgestrichen.
Die erste Zeile aber lässt sich jeweils gerade noch ausmachen.
"

Conclusion "
  **Robo**: Ich speichere dieses `E.mul_of_ne` auch mal, wer weiß.

  **Du**: Jetzt bin ich aber neugierig, wer diese Zettel hier verloren oder weggeworfen hat. Komm, lass uns weitergehen.
"

open Nat Matrix BigOperators

/---/
TheoremDoc Matrix.E.mul_of_ne as "E.mul_of_ne" in "Matrix"

-- @[inherit_doc Matrix.StdBasisMatrix.mul_of_ne]
Statement Matrix.E.mul_of_ne {n : ℕ} (i j : Fin n) {k l : Fin n} (h : j ≠ k) : E i j * E k l = 0 := by
  Hint "**Du**: Das sieht jetzt aber nach Matrizen-Multiplikation aus.
  Müsste so auch stimmen.
  "
  unfold E
  Hint (hidden := true) "**Robo**: Vergiss aber nicht, dass `simp` die Annahme `{h}` explizit braucht!"
  simp [h]

TheoremTab "Matrix"
