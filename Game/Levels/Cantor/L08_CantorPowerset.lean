import Game.Metadata
import Game.Levels.Cantor.L07_CantorDiag

World "Cantor"
Level 9

Title "Diagonalargument"

Introduction
"
**Du**: Und wie hängt das jetzt damit zusammen, dass es keine Surjektive Funktion
`f : A → Set A` gibt?

**Cantor**: Ganz einfach, nehmt `s` als die Funktion `fun x ↦ ¬ x`.

**Robo**: In Lean kann man nämlich eine Menge `U : Set A` mit dem Prädikat
`{ x : A | x ∈ U } : A → Prop` gleichsetzen, die sind per Definition dasselbe.
Damit kann man `f : A → Set A` auch als `f : A → A → Prop` sehen.

**Du**: Und `{ a | a ∉ f a }` ist `s (f a a)` für `s : (fun x ↦ ¬ x)`, alles klar.
"

open Set Function

Statement cantor_power : ∀ (f : A → Set A), ¬ Surjective f := by
  intro f
  Hint (hidden := true) "**Cantor**: Ein Widerspruchsbeweis ist die Kür der Mathematik."
  by_contra h
  Hint "**Du**: Also hier jetzt `cantor_diagonal` verwenden?"
  Hint (hidden := true) "**Robo**: Zum Beispiel mit `apply cantor_diagonal at {h}`!"
  Branch
    let _C := { a | a ∉ f a }
    Hint "**Cantor**: Nein, nein! Wir wollten doch
      mein schönes Theorem `cantor_diagonal` verwenden!"
  apply cantor_diagonal at h -- Lvl 7
  Hint (hidden := true) (strict := true) "
  **Cantor**: Wir hatten doch geübt, dass `¬(·)` keinen Fixpunkt hat.

  **Robo**: Das habe ich als `not_isFixedPt_not` gepspeichert"
  Branch
    have g1 := h (¬ ·)
    have g2 := not_isFixedPt_not
    contradiction
  apply not_isFixedPt_not -- Lvl 4
  apply h


-- the following implies `cantor_power` but not vice versa.
-- maybe add this before L01_CantorPowerSet
example (f : A → Set A) : ¬ ∃ (a : A), f a = { x | x ∉ f x } := by
  push_neg
  intro a
  intro h
  by_cases a ∈ f a
  · suffices : a ∉ f a
    · contradiction
    rw [h] at h_1
    rw [mem_setOf] at h_1
    assumption
  sorry

#check Set.preimage

example (f : A → Set A) : f ⁻¹' { { a | a ∉ f a } } = ∅ := by
 sorry



TheoremTab "Function"
