import Game.Metadata
import Game.Levels.Predicate

World "Contradiction"
Level 5

Title "Kontraposition"

Introduction
"
**Benedictus**: Gut, hier ist die angekündigte Frage. Versucht mal einen *direkten*
Beweis, ohne `by_contra`.
"

open Nat

Statement (n : ℕ) (h : Odd (n ^ 2)): Odd n := by
  Hint "
    **Robo**: Ich schlage vor, wir führen das auf das Lemma `even_square` zurück, das wir auf
    Quantus schon gezeigt hatten. Hier steht ja im Grunde `Odd (n^2) → Odd n`. Und unter
    Kontraposition ist das äquivalent zu `Even n → Even (n^2)`.

    **Du**: Richtig. Von hinten durch die Brust … Aber warte, im Moment steht da doch gar kein `→`.

    **Robo**: Erinner dich an `revert`. Mit `revert {h}` kannst du die Annahme `{h}` als
    Implikationsannahme ins Beweissziel schieben."
  revert h
  Hint "
    **Du**: Und jetzt kann ich dieses Kontrapositionslemma anwenden? Wie hieß das noch einmal?

    **Robo**: Tatsächlich kannst auch einfach `contrapose` schreiben."
  contrapose
  Hint (hidden := true) "**Robo**: Vielleicht hilft jetzt `even_iff_not_odd` weiter?"
  rw [← even_iff_not_odd]
  rw [← even_iff_not_odd]
  Hint "
    **Du**: Das sieht schon ganz gut aus. Jetzt kann ich tatsächlich das alte Lemma
    `even_square` anwenden!"
  apply even_square

NewTactic contrapose
DisabledTactic by_contra
TheoremTab "Nat"

Conclusion "**Benedictus**: Hervorragend! Ich glaube, damit seid Ihr jetzt ganz gut gewappnet."
