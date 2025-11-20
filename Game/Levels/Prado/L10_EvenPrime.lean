import Game.Metadata
import Game.Levels.Prado.L09_ExistsUnique

World "Prado"
Level 10

Title ""

/-
Introduction
"Inzwischen seid ihr auf der Dachterasse angekommen.
Aber Guino hat es inzwischen aufgegeben, alle architektonischen Details zu erklären.
Die Aussicht ist nicht schlecht.

**Robo** *(zu dir)*:  Ich glaube, wir sind so weit.
"
-/

Introduction "`INTRO` Intro Prado L10"

namespace Nat

Statement : ∃! (p : ℕ), Nat.Prime p ∧ Even p := by
  use 2
  simp
  constructor
  · decide
  · intro p hp h
    -- Hint (hidden := true) "**Robo**:
    -- Schau noch einmal genau durch die Aussagen, die wir schon gezeigt hatten."
    Hint (hidden := true) "`COMMENT` Remind former proof"
    rw [even_iff_two_dvd] at h
    rw [prime_def] at hp
    obtain ⟨h2, hprime ⟩ := hp
    apply (hprime 2) at h
    obtain h | h:= h
    · contradiction
    · symm
      assumption

TheoremTab "ℕ"

/-
Conclusion "
**Du**: Juchhu!  Und wer sagt es ihm jetzt?

**Robo**:  Vielleicht lassen wir es lieber.  Ich habe das Gefühl,
ihm gefällt ohnehin sein Museum so leer wie es ist am besten.

Ihr bedankt euch also artig für die Führung, zeigt euch tief beeindruckt
von der hiesigen Eisbaukunst, und fliegt weiter."
-/

Conclusion "`CONC` Conclusion Prado L10"
