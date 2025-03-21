import Game.Metadata

World "Babylon"
Level 1

Title ""

Introduction
"
**Babylonier**: Jeder Turm hat eine Inschrift. Da könnt ihr noch einmal genau nachlesen,
warum er steht. Hier zum Beispiel.
"

open Nat Finset
Statement (I : Finset ℕ) : (∑ i ∈ I, 1) = card I := by
  Hint "
    **Du**: Oh das ist ganz schön viel neues … mal sehen …

    Das sieht aus wie $( \\sum_\{i\\in I} 1)$ ist gleich …

    **Robo**: … der Anzahl der Element in $I$, also der Kardinalität von $I$.

    **Babylonier**: Und, könnt ihr das beweisen?

    **Robo** *(zu Dir)*: Ich würde als erstes `simp` versuchen.
    Das ist wirklich eine starke Taktik, die viele Terme vereinfacht."
  simp

TheoremTab "Sum"

Conclusion "**Babylonier**: Seht gut, das passt!"

NewDefinition Finset.card

/-
**Robo**: Mir fällt gerade ein, du hattest ja mal gefragt bezüglich `rw` unter Quantoren.
Mit Summen ist das das gleiche: Hier musst du immer `simp_rw` verwenden, wenn du innerhalb
einer Summe was umschreiben möchtest."
-/
