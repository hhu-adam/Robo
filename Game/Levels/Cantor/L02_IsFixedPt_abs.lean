import Game.Metadata
import Game.Levels.Cantor.L01_CantorPowerset

World "Cantor"
Level 3

Title "Fixpunkte"

Introduction
"
**Du**: Also wie ist das mit der Diagonalen?

**Cantor**: Um das genauer zu erläutern muss ich euch zuerst ein paar rätsel zu Fixpunkten stellen.
"

open Function Set

Statement : ∀ (x : ℝ), IsFixedPt abs x ↔ 0 ≤ x := by
  Hint "**Robo**: `IsFixedPt f x` ist die Aussage `f x = x`.

  **Du**: Und `abs` ist der Betrag? Was mache ich damit?

  **Robo**: Ich denke so einfache Sachen, die `0` beinhalten kann `simp` ganz gut,
  aber ich habe hier auch noch zwei Resultate, die hilfreich aussehen."
  Branch
    unfold IsFixedPt
    intro x
    constructor
    · intro h
      rw [← h]
      exact abs_nonneg _
    · exact abs_of_nonneg
  intro x
  constructor
  · intro h
    rw [← h]
    Branch
      simp only [abs_nonneg]
    Branch
      positivity
    simp
  · intro h
    unfold IsFixedPt
    Branch
      rw [abs_of_nonneg h]
    simp
    assumption

/---/
DefinitionDoc abs as "|·|"
/---/
DefinitionDoc Function.IsFixedPt as "IsFixedPt"

NewDefinition Function.IsFixedPt abs
NewTheorem abs_of_nonneg abs_nonneg
TheoremTab "Function"
