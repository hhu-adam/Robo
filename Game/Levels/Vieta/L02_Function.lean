import Game.Metadata


World "Vieta"
Level 2

Title "Anonyme Funktionen"

Introduction
"
Wieder saust ein Pfeil vorbei.  Aber Vieta gibt euch seelenruhig das nächste Blatt.
"

Statement : let f : ℤ → ℤ := fun x ↦ x ^ 2; f 2 = 4 := by
  Hint"
    **Robo**: Aha, das ist interessanter.  Hier ist
    `fun (x : ℤ) ↦ x ^ 2` eine „anonyme Funktion“, nämlich die Abbildung $x↦x^2$.

   **Du**:  Und was ist an ihr anonym?

   **Robo**: Na, dass sie erst einmal keinen Namen hat.
    Erst durch `f : ℤ → ℤ := …` erhält sie einen Namen.

  **Du**:  Ach so.  Ingesamt haben wir also die folgende Abbildung, ja?

    $$
    \\begin\{aligned}
      f\\colon \\mathbb\{ℤ} &\\to \\mathbb\{ℤ} \\\\
      x &\\mapsto x ^ 2
    \\end\{aligned}
    $$

  Ich soll also zeigen $2^2=4$?

  **Robo**: Ja.

  **Du**: Und wie mache ich das hier?

  **Robo**: Lean kann durch die meisten Abbildungsvorschriften hindurchsehen, also sollte `rfl`
  hier reichen. Alternativ kannst du mit `simp [{f}]` explizit die Definition einsetzen."
  Branch
    simp [f]
  rfl


NewDefinition Symbol.function
TheoremTab "Function"

Conclusion ""
