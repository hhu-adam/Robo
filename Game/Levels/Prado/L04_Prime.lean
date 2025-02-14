import Game.Metadata
import Game.Levels.Prado.L03_EvenIff

namespace Nat

World "Prado"
Level 4

Title "Primzahlen"

Introduction"
**Du**:  Gut.  Und kannst du mir jetzt zeigen, wie man mit Primzahlen arbeitet?

**Robo**: Mal sehen, ob ich eine Aufgabe zu Primzahlen auf Lager habe … Diese hier vielleicht?"


-- TODO: there is a mathlib PR to ask for this renaming: #19255
alias _root_.Nat.prime_def := prime_def_lt''

Statement (a p : ℕ) (hp : Prime p) (h : 2 ≤ a) (ha : a ∣ p) : a = p := by
  Hint "
    **Robo**: Hier ist `(hp : Prime p)` natürlich die Annahme, dass `p` eine Primzahl ist.
    Um mit dieser Annahme zu arbeiten, wendest du am besten immer `rw [prime_def] at hp` an."
  Branch
    unfold Prime at hp
    Hint "**Robo**:  Nee, lieber nicht.  Du solltest `Prime` nicht unfolden!
    Das macht alles nur schwieriger.  Benutze lieber wie ich gesagt hatte `rw [prime_def] at hp`."
  rw [prime_def] at hp
  Hint "**Du**:  Aha.  Eine Primzahl ist also eine natürlich Zahl größergleich `2`, die nur durch
`1` und sich selbst teilbar ist.  Das klingt vertraut."
  obtain ⟨hp₁, hp⟩ := hp
  Branch
    -- Marcus' solution
    have ha' : a ∣ p → a = 1 ∨ a = p
    · Hint "**Robo**:  Statt `have` könntest du hier übrigens auch `specialize {hp} {a}` verwenden."
      apply hp
    have ha'' : a = 1 ∨ a = p
    · apply ha'
      assumption
    obtain h1 | h2 := ha''
    linarith
    assumption
  Branch
    -- alternative to `specialize`
    --specialize hp a ha
    have _hp := hp a ha
    Hint "**Robo**:  Statt `have` könntest du hier übrigens auch `specialize {hp} {a} {ha}` verwenden."
  specialize hp a ha
  obtain hp | hp := hp
  · Hint (hidden := true) "**Robo**:  Probier mal `linarith`.  Das sollte den Widerspruch aufdecken, der sich aus
    `{a} = 1` und `2 ≤ {a}` ergibt."
    linarith
  · assumption

NewTactic specialize  -- wird hier en passant eingeführt
/---/
TheoremDoc Nat.prime_def as "prime_def" in "Nat"
NewTheorem Nat.prime_def
TheoremTab "Nat"

Conclusion "Guino schaut euch noch einmal über die Schulter.

**Guino**:  Ihr seid ja wirklich ganz eifrig bei der Sache!
Ich hatte schon befürchtet, ich müsste euch unterhalten.
"
