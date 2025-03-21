import Game.Metadata

import Game.Levels.Quantus

World "Spinoza"
Level 6

Title "" -- "Contradiction"

Introduction
"
**Du**: Aber hätten wir die letzte Aufgabe nicht genauso gut per Widerspruch beweisen können?

**Benedictus**: Klar. Ich dachte nur, ein zweiter Widerspruchsbeweis wäre langweilig.
Aber Ihr könnt die Aufgabe gern noch einmal probieren.
Hier, ich gebe Sie Euch mit auf die Reise.
Aber nun seht zu, dass Ihr weiterkommt!"

open Nat

Statement (n : ℕ) (h : Odd (n ^ 2)) : Odd n := by
  Hint "
    Sobald Ihr Euch sicher vom Gravitationsfeld des Asteroiden befreit habt, beugt Ihr
    Euch wieder über die Aufgabe.

    **Robo**: Okay, also diesmal fangen wir mit `by_contra g` an!"
  by_contra g
  Hint "**Robo**: Jetzt würde ich einen Widerspruch zu `Odd (n ^ 2)` führen."
  Hint (hidden := true) "**Robo**: Also `suffices d : ¬ Odd (n ^ 2)`."
  suffices d : ¬ Odd (n ^ 2)
  contradiction
  rw [←even_iff_not_odd] at *
  apply even_square
  assumption

DisabledTactic contrapose revert

Conclusion "
**Robo**: Bravo! Hier ein Überblick, was uns Benediktus gezeigt hat.


| **Taktik**      | **Zweck**                                              |
|:----------------|:-------------------------------------------------------|
| `have`          | Zwischenresultat annehmen                              |
| `suffices`      | Zwischenresultat annehmen                              |
| `by_contra`     | Widerspruchsbeweis anfangen                            |
| `contradiction` | Widerspruchsbeweis schließen                           |
| `contrapose`    | Kontraposition                                         |
| `revert`        | nützlich, um danach `contrapose` anzuwenden            |
"
