import Game.Metadata
import Game.Levels.Cantor.L07_CantorDiag

World "Cantor"
Level 8

Title "Diagonalargument"

Introduction
"
**Du**: Robo, kannst du dich and die ürsprüngliche Aufgabe erinnern?

**Robo**: Bitte sehr!
"

open Set Function

Statement cantor_power : ∀ (f : A → Set A), ¬ Surjective f := by
  intro f
  Hint (hidden := true) "**Cantor**: Ein Widerspruchsbeweis ist die Kür der Mathematik."
  by_contra h
  Hint "**Du**: Also hier jetzt `cantor_diagonal` verwenden?"
  Hint (hidden := true) "**Robo**: Zum Beispiel mit `apply cantor_diagonal at {h}`!"
  Branch
    let C := { a | a ∉ f a }
    Hint "**Cantor**: Nein, nein! Wir wollten doch
      mein schönes Theorem `cantor_diagonal` verwenden!"
  Branch
    apply not_isFixedPt_not
    Branch
      -- Mathlib states one should not use the fact that `Set A` is `A → Prop`. Instead
      -- one should use `(· ∈ ·)` and `setOf`. This would looks like the following:
      let g : A → A → Prop := fun (a b : A) => (b ∈ f a)
      apply cantor_diagonal g h (fun x => ¬x)
    Branch
      apply cantor_diagonal f h (fun x => ¬x)
    apply cantor_diagonal
    assumption
  apply cantor_diagonal at h -- Lvl 7
  Hint (hidden := true) "**Cantor**: Wir hatten doch geübt, dass `¬(·)` keinen Fixpunkt hat.

  **Robo**: Das habe ich als `not_isFixedPt_not` gepspeichert"
  apply not_isFixedPt_not -- Lvl 4
  apply h

TheoremTab "Function"
