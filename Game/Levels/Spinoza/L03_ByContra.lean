import Game.Metadata

World "Spinoza"
Level 3

Title "" -- "Widerspruch"

-- Introduction "**Benedictus**: Hier ist noch eine Variante."
Introduction "`INTRO` Intro Spinoza L03"

Statement (A B : Prop) (g : A → B) (b : ¬ B) : ¬ A := by
  /-
  Hint "
    **Robo**: Ein `¬` im Goal heißt häufig, dass du einen Widerspruchsbeweis führen
    möchtest.

    **Du**: Und wie mache ich das? Mit `contradiction`?

    **Robo**: Mit `by_contra h` fängst du einen Widerspruchsbeweis an. Und mit `contradiction`
    schließt du ihn ab."
  -/
  Hint "Explain `¬` in goal. Explain `contradiction` and `by_contra h`"
  by_contra h
  /-
  Hint "
    **Robo**: Jetzt hast du also eine Annahme `{h} : {A}`, und damit musst du einen
    Widerspruch herleiten.

    Du könntest zum Beispiel jetzt mit `suffices` sagten, welchen Widerspruch du gern herleiten
    möchtest, etwa `suffices k : B`
  "
  -/
  Hint "Apply contradiction with `{h} : {A}` via `suffices` with `suffices k : B`"
  suffices k : B
  /-
  Hint "
    **Du**: Ah, und jetzt kann ich einfach sagen dass sich die Annahmen `{B}` und `¬{B}` sich
    widersprechen."
  -/
  Hint "Finish proof by stating contradiction between `{B}` and `¬{B}`"
  contradiction
  /-
  Hint "
    **Robo**: Und jetzt musst du nur noch das Zwischenresultat herleiten, dass zu diesem
    Widerspruch geführt hat."
  -/
  Hint "Derive intermediate result that lead to the conclusion"
  apply g
  assumption

-- Conclusion "**Benedictus**: Ich sehe schon, Ihr lernt schnell!"
Conclusion "`CONC` Conclusion Spinoza L03"

NewTactic by_contra
