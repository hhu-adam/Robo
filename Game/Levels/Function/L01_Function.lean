import Game.Metadata


World "Function"
Level 1

Title "Anonyme Funktionen"

Introduction
"
Auf die Frage hin, ob sie von einer Bibliothek wisse, erzählt euch das kleine Mädchen,
dass es auf der Insel nur eine gäbe, aber sie bedrängt euch so mit einer Frage,
dass sie euch gar nicht sagt, wo dieser zu finden sei.
"

Statement : let f : ℤ → ℤ := fun x ↦ x ^ 2; f 2 = 4 := by
  -- TODO: anpassen?
  Hint"
    **Robo**: `f : ℤ → ℤ` ist die Notation für eine Funktion und `f x` ist diese Funktion
    angewendet auf ein Element `(x : ℤ)`.

    **Du**: War `→` nicht eben noch eine Implikation?

    **Robo**: Doch, die brauchen das gleiche Zeichen für beides.

    **Du**: Dann ist `f : ℤ → ℤ` also einfach abstrakt irgendeine Funktion,
    wie definiere ich aber jetzt konkret eine Abbildungsvorschrift?

    **Robo**: Man kennt hier eine Notation für eine anonyme Funktion:
    `fun (x : ℤ) ↦ x ^ 2` ist

    $$
    \\begin\{aligned}
      f : \\mathbb\{ℤ} &\\to \\mathbb\{ℤ} \\\\
      x &\\mapsto x ^ 2
    \\end\{aligned}
    $$

    **Robo**: PS, `↦` ist `\\mapsto`. Aber man kann auch stattdessen `=>` benutzen."
  rfl


NewDefinition Symbol.function
TheoremTab "Function"

Conclusion
"
Das Mädchen wird kurz ruhig, dann beginnt es zu lächeln und zeigt strahlend
in eine Richtung. Ihr folgt ihrem Finger und euch fällt in weiter ferne eine pompöse Struktur
auf einem flachen Hügel auf.
"
