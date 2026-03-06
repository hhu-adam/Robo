
import Game.Metadata

World "Piazza"
Level 1

Title ""

/-
Introduction
"
**Fin**:  Ja, klar.  Das hier zum Beispiel.
"
-/
Introduction "Intro Piazza L01"

open Set

Statement : 1 ∈ ({1, 6, 4} : Set ℕ) := by
  /-
  Hint "
    **Du**:  Verstehe ich das richtig?

    **Robo**: Vermute schon.  Sieht ziemlich *tauto*logisch aus, nicht?
    "
  -/
  Hint "Try tauto"
  tauto

NewDefinition Mem Set
TheoremTab "Set"

/-
Conclusion "
**Set**:  Ihr kennt euch also auch schon ein bisschen mit Mengen aus?

**Robo**:  Naja, ein *bisschen*.
"
-/
Conclusion "Conclusion Piazza L01"
