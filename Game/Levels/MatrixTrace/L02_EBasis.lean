import Game.Levels.MatrixTrace.L01_SMulEBasis

World "Trace"
Level 2

Title "Falsche Indizes"

-- TODO: Do we need this level??

Introduction
"
Kurze Zeit später findet ihr einen sehr ähnlichen Zettel, wieder
vollgekritzelt, fast alles durchgestrichen.
Die erste Zeile aber lässt sich gerade noch ausmachen.
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
  Hint "**Du**: Vielleicht sind das wirklich irgendwelche Tipps. Der hier scheint
  ganz ähnlich zu funktionieren: Wenn man zwei Standardmatrizen zusammenzählt und die Indizes nicht stimmen, erhält man Null.
  "
  unfold E
  Hint (hidden := true) "**Robo**: Vergiss aber nicht, dass `simp` die Annahme `{h}` explizit braucht!"
  simp [h]

NewDefinition Matrix.E
TheoremTab "Matrix"
