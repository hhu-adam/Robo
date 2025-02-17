import Game.Metadata
import Game.Levels.Prado.L07_ExistsUnique

namespace Nat

World "Prado"
Level 8

Title "Gerade Primzahlen"

Introduction
"Inzwischen seid ihr auf der Dachterasse angekommen.
Guino ist etwas konsterniert, dass ihr euch so wenig für die Architektur interessiert.

**Robo** *(zu dir)*:  Jetzt sind wir aber, glaube ich, so weit.
Ich hoffe, die Aussagen, die wir schon gezeigt haben, sind irgendwie hilfreich.
"

Statement : ∃! (p : ℕ), Nat.Prime p ∧ Even p := by
  use 2
  simp
  constructor
  · decide
  · intro y h₁ h₂
    Hint (hidden := true) "**Robo**:
    Schau noch einmal genau durch die Aussagen, die wir schon gezeigt hatten."
    rw [even_iff_two_dvd] at h₂
    rw [prime_dvd_prime_iff_eq] at h₂
    · symm
      assumption
    · decide
    · assumption

TheoremTab "ℕ"

Conclusion "
**Du**: Juchhu!  Und wer sagt es ihm jetzt?

**Robo**:  Vielleicht lassen wir es lieber.  Ich habe das Gefühl,
ihm gefällt ohnehin sein Museum so leer wie es ist am besten.

Ihr bedankt euch also artig für die Führung, zeigt euch tief beeindruckt
von der hiesigen Eisbaukunst, und fliegt weiter zum nächsten Planeten."
