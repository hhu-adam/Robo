import Game.Levels.Samarkand.L01_ImagePreimage

open Set

World "Samarkand"
Level 2
Title "" -- "Bild/Urbild"

-- Introduction "Arapuka diktiert euch noch eine Aufgabe."
Introduction "`INTRO` Intro Samarkand L02"

Statement {A B C : Type} (f : A → B) (g : B → C) : image (g ∘ f) = (image g) ∘ (image f) := by
  /-
  Hint "
    **Du**:  Aha!  Ich kann also auch einfach `image` schreiben, wenn ich mir diese Fliegendreck-Schreibweise mit `''` nicht mag?

    **Robo**:  Nein, schau mal genauer hin.   Hier ist `image f` eine Abbildung.
    Es ist natürlich genau die Abbildung, die eine Teilmenge von `A` auf die entsprechende Bildmenge in `B` wirft, also
    ```
    image f = fun S ↦ f '' S
    ```
    Du kannst also `image f` durch `f ''` ausdrücken, aber nicht umgekehrt.
  "
  -/
  Hint "Can not use `image` instead of `''`. Explain that `image f` is mapping from `A` to `B`. You can express `image f` by `f ''` but not vica versa"
/-
This is literally true:
example : image f = fun S ↦ f '' S := by
  rfl
--/
  /-
  Hint (hidden := true) "
    **Robo**:  Zu zeigen ist die Übereinstimmung von zwei Abbildungen.  Erinnerst du dich an `funext`?
  "
  -/
  Hint (hidden := true) "Remind `funext`"
  Branch
    funext
    /-
    Hint "
      **Robo**:  Oh, nein.  Das sieht zu kompliziert aus.  Schreib mal lieber explizit `funext S`.
      "
    -/
    Hint "try `funext S`"
  funext S
  /-
  Hint (hidden := true) "
    **Robo**:  Jetzt ist die Gleichheit von zwei Mengen zu zeigen – `ext` heißt das Zauberwort.
    "
  -/
  Hint (hidden := true) "Try `ext`"
  ext c
  /-
  Hint (hidden := true) "
    **Robo**:  Das kann man bestimmt leicht vereinfachen …
  "
  -/
  Hint (hidden := true) "Try simplification"
  simp

NewDefinition Set.image Set.preimage

/-
Conclusion "
  **Arapuka**:  Hübsch, hübsch.
"
-/
Conclusion "`CONC` Conclusions Samarkand L02"
