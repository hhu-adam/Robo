import Game.Metadata
import Game.Levels.Prado.L05_One

namespace Nat

World "Prado"
Level 6

Title ""

Introduction
"
Jetzt eine etwas schwierigere Aussage, aber du hast alle Tools dafür!
"

Statement prime_dvd_prime_iff_eq {a b : ℕ} (ha : Prime a) (hb : Prime b) :
    a ∣ b ↔ a = b := by
  constructor
  · intro h
    Hint (hidden := true) "Die Annahme `Prime {b}` wirst du mit `prime_def` umschreiben müssen,
    die Annahme `Prime {a}` hingegen würde ich so lassen wie sie ist!"
    rw [prime_def] at hb
    obtain ⟨_hb_two, hb⟩ := hb
    apply hb at h
    Hint "Du kannst eine Fallunterscheidung auf `{h}` mit `obtain h | h := {h}`
    machen. Denk aber dran, dass dieser Strich `|` der normale Strich auf der Tastur ist, während
    Teilbarkeit mit `∣` (`\\dvd`) einen anderen Strich verwendet!"
    obtain h | h := h
    · Hint "Findest du den Widerspruch?"
      Hint (hidden := true) (strict := true) "Mach mal `have := not_prime_one`"
      have h₂ := not_prime_one
      rw [← h] at h₂
      contradiction
    · assumption
  · intro h
    rw [h]

TheoremTab "Nat"
