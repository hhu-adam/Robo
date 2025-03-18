import Game.Metadata
import Game.Levels.Prado.L02_Dvd

namespace Nat

World "Prado"
Level 3

Title ""

Introduction
"Um Guino bei Laune zu halten, fragt Robo vorsichtig,
ob er euch nicht eine Aufgabe stellen möchte.
Er gibt euch folgende Variation seiner vorherigen Aufgabe.
"

Statement : ∃ p : ℕ, Prime p ∧ p ∣ 67280421310721 := by
  Hint "**Du** *(zu Robo)*:  Hast du eine Idee, was hier ein Primfaktor sein könnte?

  **Robo**: Nö.

  Robo überlegt.

  **Robo**:  Ist doch aber auch egal.  Er hat ja gar nicht nach einem konkreten Faktor gefragt,
  sondern nur nach der Existenz irgendeines Primfaktors.  Aber das ist trivial.
  Lass mich überlegen … ich glaube `exists_prime_and_dvd` ist die Aussage, die du hier brauchst.
  "
  apply exists_prime_and_dvd
  simp

TheoremTab "ℕ"
