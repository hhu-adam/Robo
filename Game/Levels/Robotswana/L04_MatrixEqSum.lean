import Game.Levels.Robotswana.L03

World "Robotswana"
Level 4

Title "" -- "Summe von Basiselementen"

/-
Introduction "Ihr kommt an eine Stelle, wo das Gras auf einer größeren, quadratischen
Fläche heruntergetrampelt ist. Spuren führen kreuz und quer und in verschiedene
Richtungen weg.

Ein bisschen planlos sucht ihr die Stelle ab und findet verschiedenste Pergamentstücke.
Die meisten sind leer oder unleserlich, aber eines kannst du entziffern."
-/
Introduction "`INTRO` Intro Robotswana L04"

/-
Conclusion "
Du beschließt, einer besonders markanten Spur zu folgen. Robo zieht dir hinterher und schnappt
sich beim gehen noch ein willkürliches Stück Pergament vom Boden.
"
-/
Introduction "`CONC` Conclusion Robotswana L04"

open Nat Matrix -- BigOperators

/-- Sagt aus, dass man jede $(n × n)$-Matrix (über $\mathbb{R}$) $A$ schreiben kann
als $A = \sum_{i=0}^{n-1}\sum_{j=0}^{n-1} A_{ij} \cdot E(i, j)$.

Siehe auch `matrix_eq_sum_single`, welches die generalisierte Form für
$(m × n)$-Matrix (über beliebigem $R$) ist. -/
TheoremDoc Matrix.matrix_eq_sum_ebasis as "matrix_eq_sum_ebasis" in "Matrix"

Statement Matrix.matrix_eq_sum_ebasis {n : ℕ} (A : Mat[n,n][ℝ]) :
    A = ∑ i : Fin n, ∑ j : Fin n, (A i j) • E i j := by
  -- Hint "**Du**: Das scheint einfach zu sagen, dass diese `E i j` ein Erzeugendensystem für den Raum der Matrizen bilden.
  --
  --  **Robo**: Da kannst du bestimmt gleich die Resultate anwenden, die wir schon gefunden haben!"
  Hint "Explain statement w.r.t. `E i j` and use former results"
  /-
  Hint (hidden := true) "**Robo**: Den Ausdruck `(A i j) • E i j` kannst du doch bestimmt mit `Matrix.smul_ebasis` vereinfachen.

  **Du**: Also `rw […]`?

  **Robo**:  Nein, unter der Summe wird das nicht funktionieren.
  Aber `simp […]` hat Aussicht auf Erfolg."
  -/
  Hint (hidden := true) "Expression `(A i j) • E i j` can be simplified with `Matrix.smul_ebasis`.
  `rw […]` can not be used under a sum. `simp […]` can work.
  "
  Branch
    unfold E
    /-    Hint "**Robo**: Ja gut, du kannst auch einfach den Beweis vom ersten Pergament wiederholen.
    Nur zu, Übung macht den Meister.

    **Du**: Schon gut, ich hab kein mechanisches Hirn wie du."
    -/
    Hint "Repeat proof from first level"
    simp
    /- should now be the same proof state as after
       the `simp [Matrix.smul_ebasis] in the next line -/
  simp [Matrix.smul_ebasis] -- Lvl 1
  /-
  Hint "**Robo**: Ach ja!  So wie es jetzt hier steht, kenne ich die Aussage aus meiner Bibliothek.
  Das ist genau `apply matrix_eq_sum_single`.

  **Du**: Super! Dann brauchen wir uns ja gar nicht damit aufhalten."
  -/
  Hint "Try to use `apply matrix_eq_sum_single`"
  apply matrix_eq_sum_single

TheoremDoc Matrix.matrix_eq_sum_single as "matrix_eq_sum_single" in "Matrix"
NewTheorem Matrix.matrix_eq_sum_single

TheoremTab "Matrix"
