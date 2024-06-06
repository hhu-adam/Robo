import Game.Metadata

import Game.Levels.Sum.L05_SumOdd
open BigOperators
open Finset

World "Sum"
Level 6

Title "Summe vertauschen"

Introduction
"
**Babylonier**: Schaut mal, da vorn stehen zwei Freunde von mir. Ich muss euch unbedingt vorstellen!

Die beiden Freunde stehen vor zwei Türmen mit einer kleinen Brücke, die zwischen den ihnen verläuft.
Aber die Tafel am Eingang ist so sehr verwittert, dass sie nicht mehr lesbar ist.
Auf der oberen Hälfte steht nur folgendes, *in einer Form, die Du verstehst*:

$$\\sum_{i=0}^n\\sum_{j=0}^m a_{ij} = \\sum_{j=0}^m\\sum_{i=0}^n a_{ij}$$

Natürlich fangt ihr an zu rätseln, was darunter stand.

**Robo**: Probier mal, das im lokalen Dialekt zu formulieren.
"


Statement
(n m : ℕ) : ∑ i : Fin n, ∑ j : Fin m, (2 ^ i * (1 + j)) =
    ∑ j : Fin m, ∑ i : Fin n, (2 ^ i * (1 + j)) := by
  Hint "**Robo**: Das sieht gut aus, aber du solltest das kurz beweisen, um sicher zu sein.

  **Du**: Hast du nicht ein Lemma dafür?

  **Robo**: Doch, probier mal `sum_comm`."
  rw [Finset.sum_comm]

NewTheorem Finset.sum_comm
TheoremTab "Sum"

Conclusion "
  Die drei Babylonier sind begeistert, als ihr ihnen das Stück Papier überreicht,
  auf das du die Aussage gekritzelt hast. Gleich zückt einer einen Meißel und sie beginnen, eine
  neue Platte zu erstellen.

  Ihr beschließt, euch noch ein bisschen allein umzusehen.
"
