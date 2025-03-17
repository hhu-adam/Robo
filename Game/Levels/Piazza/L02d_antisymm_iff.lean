import Game.Metadata

World "Piazza"
Level 5

Title "" -- "Antisymmetrie"

Introduction
"
**Set**: Und ich mag Äquivalenz
"

open Set

/---/
TheoremDoc Set.Subset.antisymm_iff as "Subset.antisymm_iff" in "Set"

Statement Set.Subset.antisymm_iff {α : Type} {A B : Set α} : A = B ↔ A ⊆ B ∧ B ⊆ A := by
  Hint "**Du**:  Ja, ich glaube, so habe ich das einmal gelernt
  – zwei Mengen sind gleich, wenn sie sich wechselseitig enthalten."
  Hint (hidden := true) "**Robo**:  Ich weiß nicht, aber ich würde mit `constructor` anfangen."
  constructor
  · intro h
    Hint (hidden := true) "**Robo**: Ersetz mal `{A}` durch `{B}`."
    rw [h]
    tauto
  · intro h
    Hint (hidden := true) "**Robo**: Ab hier müsste das Schema von eben wieder passen."
    ext i
    tauto

NewDefinition Subset

TheoremTab "Set"

Conclusion ""
