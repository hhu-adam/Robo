import Game.Levels.MatrixTrace.L02_EBasis

World "Trace"
Level 3

Title "Summe von Basiselementen"

Introduction "Ihr kommt an eine Stelle, wo das Gras auf einer grösseren, quadratischen
Fläche heruntergetreten ist. Spuren führen kreuz und queer und in verschiedene
Richtungen weg.

Ein bisschen planlos sucht ihr die Stelle ab und findet verschiedenste Pergamentstücke.
Die meisten sind leer oder unleserlich, aber eines kannst du entziffern."

Conclusion "
Du beschliesst einer besonders markanten Spur zu folgen. Robo zieht dir hinterher und schnappt
sich beim gehen noch ein willkürliches Stück Pergament vom Boden.
"

open Nat Matrix BigOperators StdBasisMatrix

/-- Sagt aus, dass man jede $(n × n)$-Matrix (über $\mathbb{R}$) $A$ schreiben kann
als $A = \sum_{i=0}^{n-1}\sum_{j=0}^{n-1} A_{ij} \cdot E(i, j)$.

Siehe auch `matrix_eq_sum_std_basis`, welches die generalisierte Form für
$(m × n)$-Matrix (über beliebigem $R$) ist. -/
TheoremDoc Matrix.matrix_eq_sum_ebasis as "matrix_eq_sum_ebasis" in "Matrix"

/-- Die generellere Version von `matrix_eq_sum_ebasis`. Siehe dort. -/
TheoremDoc Matrix.matrix_eq_sum_std_basis as "matrix_eq_sum_std_basis" in "Matrix"

Statement Matrix.matrix_eq_sum_ebasis {n : ℕ} (A : Mat[n,n][ℝ]) :
    A = ∑ i : Fin n, ∑ j : Fin n, (A i j) • E i j := by
  Hint "**Du**: Eine Matrix kann man als Summe von Basismatrizen schreiben, soweit so gut…

    **Robo**: Da kann ich ja gleich die Resultate anwenden, die wir soeben gefunden haben!"
  Hint (hidden := true) "**Robo**: Unter Summen braucht man `simp_rw`."
  Branch
    unfold E
    Hint "**Robo**: Naja, jetzt führst du den Beweis vom ersten Pergament einfach nochmals,
    aber nur zu, Übung macht den Meister.

    **Du**: Schon gut, ich hab kein mechanisches Hirn wie du."
    simp
  simp_rw [Matrix.smul_ebasis] -- Lvl 1
  Hint "**Robo**: Diese Form kenne ich aus meiner Bibliothek, das ist
  `apply matrix_eq_sum_std_basis`.

  **Du**: Danke, das möchte ich eh nicht manuell machen."
  apply matrix_eq_sum_std_basis

NewTheorem Matrix.matrix_eq_sum_std_basis
TheoremTab "Matrix"
