import Game.Metadata

World "Piazza"
Level 6

Title ""

/-
Introduction
"
**Ext**:  Ich mag *diese* Gleichung.
"
-/
Introduction "Intro Piazza L06"

open Set

Statement (A B : Set ℕ) :
    univ \ (A ∩ B) = (univ \ A) ∪ (univ \ B) ∪ (A \ B) := by
  -- Hint (hidden := true) "**Robo**: Diesmal kannst du einfach wieder `ext` verwenden."
  Hint (hidden := true) "Try `ext`"
  ext i
  -- Hint (hidden := true) "**Robo**: Und jetzt natürlich wieder `simp`."
  Hint (hidden := true) "Perform `simp` again"
  simp
  tauto

NewDefinition SDiff
TheoremTab "Set"

/-
Conclusion "
  **Du** *(zu Robo)*:  Warum heißt ext eigentlich ext?

  **Robo**:  Woher soll ich wissen, woher der Junge seinen Namen hat??

  **Du**: Nein, ich meine dieses `ext` hier!

  **Robo**: Ach so. Das Prinzip, dass zwei Mengen genau dann gleich sind,
  wenn sie dieselben Elemente besitzen, nennen Logiker *extensionality*.
  Und daraus haben die Formalosophen wohl *ext* gemacht, weil es ihnen sonst zu lang war.
"
-/

Conclusion "Conclusion Piazza L06: Explain that `ext` means extensionality"
