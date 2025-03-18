import Game.Metadata
import Game.Levels.Prado.L04_99


World "Prado"
Level 5

Title ""

Introduction
"**Du** *(zu Robo)*:  Gib mir mal wieder etwas Interessanteres!

**Robo**:  Wie wäre es hiermit?
"

/---/
TheoremDoc not_dvd_of_between_consec_multiples as "not_dvd_of_between_consec_multiples" in "ℕ"

open Nat
Statement not_dvd_of_between_consec_multiples {m n k : ℕ} (h1 : n * k < m) (h2 : m < n * (k + 1)) : ¬n ∣ m := by
  Hint "
  **Du**: `by_contra`?

  **Robo**:  Das könnte funktionieren.
  Und wahrscheinlich wirst du das Lemma `lt_of_mul_lt_mul_left` brauchen.
  Für `a b c : ℕ` zieht es aus der Annahme `a * b < a * c` den Schluss `b < c`.
  "
  by_contra h_dvd
  obtain ⟨a, ha⟩ := h_dvd
  rw [ha] at h1 h2
  apply lt_of_mul_lt_mul_left at h1  -- needs to be supplied as a hint
  apply lt_of_mul_lt_mul_left at h2  -- Note: Nat. is necessary here!
  omega

/---/
TheoremDoc lt_of_mul_lt_mul_left as "lt_of_mul_lt_mul_left" in "ℕ"
/---/
TheoremDoc lt_of_mul_lt_mul_right as "lt_of_mul_lt_mul_right" in "ℕ"
NewTheorem lt_of_mul_lt_mul_left lt_of_mul_lt_mul_right

TheoremTab "ℕ"
