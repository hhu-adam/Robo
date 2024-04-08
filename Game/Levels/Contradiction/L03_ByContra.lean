import Game.Metadata

World "Contradiction"
Level 3

Title "Widerspruch"

Introduction "**Benedictus**: Hier ist noch eine Variante."

Statement (A B : Prop) (g : A → B) (b : ¬ B) : ¬ A := by
  Hint "
    **Robo**: Ein `¬` im Goal heißt häufig, dass du einen Widerspruchsbeweis führen
    möchtest.

    **Du**: Und wie mache ich das? Mit `contradiction`?

    **Robo**: Mit `by_contra h` fängst du einen Widerspruchsbeweis an. Und mit `contradiction`
    schließt du ihn ab."
  by_contra h
  Hint "
    **Robo**: Jetzt hast du also eine Annahme `{h} : {A}`, und damit musst du einen
    Widerspruch herleiten.

    Du könntest zum Beispiel jetzt mit `suffices` sagten, welchen Widerspruch du gern herleiten
    möchtest, etwa `suffices k : B`
  "
  suffices k : B
  Hint "
    **Du**: Ah, und jetzt kann ich einfach sagen dass sich die Annahmen `{B}` und `¬{B}` sich
    widersprechen."
  contradiction
  Hint "
    **Robo**: Und jetzt musst du nur noch das Zwischenresultat herleiten, dass zu diesem
    Widerspruch geführt hat."
  apply g
  assumption

Conclusion "**Benedictus**: Ich sehe schon, Ihr lernt schnell!"

NewTactic by_contra
