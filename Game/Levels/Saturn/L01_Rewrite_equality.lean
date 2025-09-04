import Game.Metadata

World "Saturn"
Level 1

Title ""

Introduction "Plötzlich erreicht euch ein Funkspruch."

Statement (a b c d : ℝ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = c := by
  Hint "**Du**: Ich habe das Gefühl, das habe ich schon einmal gesehen.

  **Robo**:  Ja!  Das sieht so ähnlich aus wie eine Aufgabe, die wir auf *Implis*
  schon gelöst hatten.
  Nur, das hier jetzt Gleichheiten von Zahlen statt Genau-Dann-Wenn-Aussagen stehen!
  Aber das macht im Grunde gar keinen Unterschied.
  Du kannst `=` und `↔` mit `rw` praktisch gleich behandeln."

  Hint (hidden := true) "**Du**: Also auch `rw [hₓ]` und `rw [← hₓ]`?

  **Robo**: Probiers doch einfach."
  rw [h₁]
  Hint (hidden := true) "**Du**: Wie war das nochmals mit rückwärts umschreiben?

  **Robo**: `←` ist `\\l`. Und dann `rw [← hₓ]`"
  rw [←h₂]
  assumption

Conclusion "
  Es kommt ein 👍 zurück.
  "
#min_imports
