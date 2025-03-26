import Game.Metadata

World "Saturn"
Level 4

Title ""

Introduction "Der nächste Funkspruch sieht ein bisschen anders aus."

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
  Wieder kommt ein 👍 zurück.

  Dann möchte der anonyme Funker wissen, ob ihr bereit seid für das End Game,
  oder ob ihr lieber noch ein paar Runden um seinen Planeten kreisen wollt.

  “Bereit” funkt Robo zurück.
  "
-- The following theorems are only added for symmetry/completeness:

/---/
TheoremDoc add_comm as "add_comm" in "+ *"

/---/
TheoremDoc add_assoc as "add_assoc" in "+ *"

/---/
TheoremDoc mul_add as "mul_add" in "+ *"

/---/
TheoremDoc add_mul as "add_mul" in "+ *"

NewTheorem add_comm add_assoc mul_add add_mul
