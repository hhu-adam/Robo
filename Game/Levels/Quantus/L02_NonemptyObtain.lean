import Game.Metadata


World "Quantus"
Level 2

Title ""

/-
Introduction
"
Auf der Rückseite steht folgendes.
"
-/
Introduction "`INTRO` Intro Quantus L02"

Statement (A : Type) (h : Nonempty A) : ∃ a : A, a = a := by
  /-
  Hint "
    **Du**: Was ist das denn jetzt?  `A` ist in „Typ“?

    **Robo** Du kannst dir `A` einfach als Menge vorstellen …

    **Du** … die laut Annahme `h` nicht leer ist?

    **Robo** Genau.

    **Du** Und zeigen soll ich, dass es ein Element in `A` gibt?

    **Robo** Richtig.

    **Du** Und folgt das nicht genau aus der Annahme?

    **Robo** Das ist wieder so ein Annahme, die man mit `obtain` „zerlegen“ kann.
    Probier mal `obtain ⟨a⟩ := h`.
  "
  -/
  Hint "`A` is in 'type', whcih can be interpreted as `A` being a set which is by assumption `h`
  not empty. The goal is to show that there is an element in `A`. Use `obtain` to disect assumption.
  Try `obtain ⟨a⟩ := h`."
  obtain ⟨a⟩ := h
  use a

NewDefinition Exists

-- Conclusion "Ihr erhaltet einen bescheidenen Applaus.  Die Formalosophinnen tuscheln untereinander."
Conclusion "`CONC` Conclusion Quantus L02"
