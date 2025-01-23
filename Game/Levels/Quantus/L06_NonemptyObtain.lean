import Game.Metadata


World "Quantus"
Level 6

Title ""

Introduction
"
Ihr habt nun alle Fragen aus dem königlichen Päckchen beantwortet, und die Formalosophinnen
applaudieren. Dann wollen Sie aber auch noch ein paar Fragen stellen, aber sie können sich
nicht einigen, welche.  Nach einer Weile taucht folgendes Papier auf.
Ihr studiert es, während die Menge weiter diskutiert.
"

Statement (A : Type) (h : Nonempty A) : ∃ a : A, a = a := by
  Hint "
    **Was ist das denn jetzt?  `A` ist in „Typ“?

    **Robo** Du kannst dir `A` einfach als Menge vorstellen …

    **Du** … die laut Annahme `h` nicht leer ist?

    **Robo** Genau.

    **Du** Und zeigen soll ich, dass es ein Element in `A` gibt?

    **Robo** Richtig.

    **Du** Und folgt das nicht genau aus der Annahme?

    **Robo** Das ist wieder so ein Annahme, die man mit `obtain` „zerlegen“ kann.
    Probier mal `obtain ⟨a⟩ := h`.
  "
  obtain ⟨a⟩ := h
  use a

NewDefinition Exists

Conclusion ""
