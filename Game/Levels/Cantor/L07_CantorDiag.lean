import Game.Metadata
import Game.Levels.Cantor.L07_CantorDiag_IsFixedPt

World "Cantor"
Level 9

Title "Diagonalargument"

Introduction
"
**Cantor**: Viel Glück!
"

Conclusion "**Du**: Jetzt möchte ich aber mit dieser generellen Form, die ursprüngliche
Aufgabe nochmals lösen."

open Function Set

Statement cantor_diagonal (f : A → A → Y) (hsurj : Surjective f) (s : Y → Y) :
    ∃ x, IsFixedPt s x := by
  Hint (strict := true) "**Cantor**: Mit der Aufgabe vorhin könnt
  ihr sicher herausfinden, was das richtige `c : A → Y` ist, auf das ihr die Surjektivität
  anwenden wollt."
  Hint (hidden := true) (strict := true) "**Robo**: So viel weiss ich: die Funktion
  definieren wir mit

  ```
  let c : A → Y := fun a ↦ _
  ```

  aber den Wert musst schon du herausfinden!
  "
  let c : A → Y := fun (a : A) ↦ s (f a a)
  Hint "**Cantor**: Gute Wahl!"
  rcases hsurj c with ⟨a, ha⟩
  use (f a a)
  Hint (hidden := true) "**Cantor**: Das sieht gut aus, jetzt können wir ja
  `cantor_diagonal_isFixedPt` von vorhin brauchen!"
  apply cantor_diagonal_isFixedPt c
  · simp
  · assumption

TheoremTab "Function"
