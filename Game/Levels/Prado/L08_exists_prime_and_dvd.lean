import Game.Metadata
import Game.Levels.Prado.L07_dvd_mul

World "Prado"
Level 8

Title ""

Introduction
"Um Guino bei Laune zu halten, fragt Robo vorsichtig,
ob er euch nicht eine Aufgabe stellen möchte.
Er gibt euch folgende Variation seiner vorherigen Aufgabe.
"

namespace Nat

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


/---/
TheoremDoc Nat.exists_prime_and_dvd as "exists_prime_and_dvd" in "ℕ"
NewTheorem Nat.exists_prime_and_dvd

TheoremTab "ℕ"

Conclusion "
  **Guino:** Na gut, lasst uns weitergehen.  Schaut mal, ist das nicht eine herrlich Treppe?
  Wir gehen hoch!

  **Du** *(zu Robo)*: Lass uns doch jetzt einmal probieren, die Aussage zu formlieren, die wir Guino zeigen wollen.
  Es gibt genau eine gerade …

  **Robo**:  Halt!  „Genau eine“ hatten wir noch nicht.
"
