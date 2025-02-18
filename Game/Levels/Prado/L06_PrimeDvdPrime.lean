import Game.Metadata
import Game.Levels.Prado.L05_One

namespace Nat

World "Prado"
Level 6

Title ""

Introduction
"
**Robo**:  Ich habe in meiner Sammlung noch folgende Aussage gefunden, die relevant sein könnte.
Mal sehen, ob wir die jetzt zusammen gezeigt bekommen.
"
/---/
TheoremDoc Nat.prime_dvd_prime_iff_eq as "prime_dvd_prime_iff_eq" in "ℕ"

Statement prime_dvd_prime_iff_eq {a b : ℕ} (ha : Prime a) (hb : Prime b) :
    a ∣ b ↔ a = b := by
  Hint "**Du**:  Die eine Primzahl teilt die andere genau dann, wenn sie beide gleich sind?

  **Robo**: Genau."
  constructor
  · intro h
    Hint (hidden := true) "**Robo**:  Die Annahme `Prime {b}` wirst du natürlich wieder mit `prime_def` umschreiben müssen.
    Die Annahme `Prime {a}` kannst du vielleicht lassen, wie sie ist!"
    rw [prime_def] at hb
    obtain ⟨_hb_two, hb⟩ := hb
    apply hb at h
    Hint "**Robo**:  Denk daran, dass du eine Fallunterscheidung mit `obtain h | h := {h}`
    machen kannst.
    (Hier ist `|` der normale Strich, nicht der Teilbarkeitsstrich `∣` (`\\dvd`).)"
    obtain h | h := h
    · Hint "**Robo**: Findest du jetzt vielleicht einen Widerspruch?"
      Hint (hidden := true) (strict := true) "**Robo**: Mach mal weiter mit `have h' := not_prime_one`."
      have h' := not_prime_one
      rw [← h] at h'
      contradiction
    · assumption
  · intro h
    rw [h]

TheoremTab "ℕ"

Conclusion "**Du**:  Sehr schön.
Dann lass uns doch jetzt einmal probieren, die Aussage zu formlieren, die wir Guino zeigen wollen.
Es gibt genau eine gerade …

**Robo**:  Halt!  „Genau eine“ hatten wir noch nicht.
"
