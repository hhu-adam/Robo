import Game.Metadata
import Game.Levels.Prado.L06_Prime_Specialize__prime_def


World "Prado"
Level 7

Title ""

Introduction "
  **Robo**:  Hier ist noch eine kleine Primzahl-Aufgabe.
   Das Lemma `Prime.dvd_mul` sagt, dass eine Primzahl genau dann ein Produkt teilt,
   wenn sie einen der Faktoren teilt.  Das musst du hier nur anwenden.
   "

namespace Nat

Statement (a b : ℕ) : 5 ∣ (a * b) ↔  5 ∣ a ∨ 5 ∣ b := by
  rw [Prime.dvd_mul]
  decide

/---/
TheoremDoc Nat.Prime.dvd_mul as "Prime.dvd_mul" in "ℕ"
NewTheorem Nat.Prime.dvd_mul

TheoremTab "ℕ"

Conclusion "**Du** Du stellst aber wirklich sehr einfache Aufgaben."
