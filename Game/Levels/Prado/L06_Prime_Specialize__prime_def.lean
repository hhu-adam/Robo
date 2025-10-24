import Game.Metadata
import Game.Levels.Prado.L05_not_dvd_of_between_consec_multiples

World "Prado"
Level 6

Title ""

/-
Introduction"
**Du**:  Gut.  Und kannst du mir jetzt zeigen, wie man mit Primzahlen arbeitet?

**Robo**: Mal sehen, ob ich eine Aufgabe zu Primzahlen auf Lager habe … Diese hier vielleicht?"
-/
Introduction "`INTRO` Intro Prado L06"

namespace Nat

Statement (a p : ℕ) (hp : Prime p) (h : 2 ≤ a) (ha : a ∣ p) : a = p := by
  -- Hint "
  --  **Robo**: Hier ist `(hp : Prime p)` natürlich die Annahme, dass `p` eine Primzahl ist.
  --  Um mit dieser Annahme zu arbeiten, wendest du am besten immer `rw [prime_def] at hp` an."
  Hint "Try `rw [prime_def] at hp`"
  Branch
    unfold Prime at hp
    -- Hint "**Robo**:  Nee, lieber nicht.  Du solltest `Prime` nicht unfolden!
    -- Das macht alles nur schwieriger.  Benutze lieber wie ich gesagt hatte `rw [prime_def] at hp`."
    Hint "Try `rw [prime_def] at hp`"
  rw [prime_def] at hp
  -- Hint "**Du**:  Aha.  Eine Primzahl ist also eine natürlich Zahl größergleich `2`, die nur durch
  -- `1` und sich selbst teilbar ist.  Das klingt vertraut."
  Hint "Explain prime number"
  obtain ⟨hp₁, hp⟩ := hp
  /-
  Hint "
    **Du**: Ich will `{hp}` jetzt bestimmt auf `{a}` anwenden, oder?

    **Robo**:  Dann sag doch `have hp' := {hp} {a}`.  Oder etwas eleganter:
    `specialize {hp} {a}`.
  "
  -/
  Hint "Try `have hp' := {hp} {a}` | `specialize {hp} {a}`"
  Branch
    -- Marcus' solution
    have ha' : a ∣ p → a = 1 ∨ a = p
    · -- Hint "**Robo**:  Statt `have` könntest du hier übrigens auch `specialize {hp} {a}` verwenden."
      apply hp
    have ha'' : a = 1 ∨ a = p
    · apply ha'
      assumption
    obtain h1 | h2 := ha''
    linarith
    assumption
  Branch
    -- alternative to `specialize`
    have _hp := hp a ha
    -- Hint "**Robo**:  Statt `have` könntest du hier übrigens auch `specialize {hp} {a} {ha}` verwenden."
  specialize hp a ha
  obtain hp | hp := hp
  --· Hint (hidden := true) "**Robo**:  Probier mal `linarith`.  Das sollte den Widerspruch aufdecken, der sich aus
  --  `{a} = 1` und `2 ≤ {a}` ergibt."
  · Hint (hidden := true) "Try `linarith"
    linarith
  · assumption

NewTactic specialize
-- Wird hier en passant eingeführt.
-- Sollte in jedem Fall in Hints erwähnt werden,
-- sonst ist es verwirrend, dass die Taktik auf
-- einmal im Inventory erscheint.
/---/
TheoremDoc Nat.prime_def as "prime_def" in "ℕ"
NewTheorem Nat.prime_def
TheoremTab "ℕ"

-- Conclusion ""
Conclusion "Conclusion Prado L06"
