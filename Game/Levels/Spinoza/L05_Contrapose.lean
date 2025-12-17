import Game.Metadata
import Game.Levels.Quantus

World "Spinoza"
Level 5

Title "" -- "Kontraposition"

/-
Introduction
"
**Benedictus**: Gut, hier ist die angekündigte Frage. Versucht mal einen *direkten*
Beweis, ohne `by_contra`.
"
-/
Introduction "Intro Spinoza L05. prove without `by_contra`"

open Nat

Statement (n : ℕ) (h : Odd (n ^ 2)): Odd n := by
  /-
  Hint "
    **Robo**: Ich schlage vor, wir führen das auf das Lemma `even_square` zurück, das wir auf
    Quantus schon gezeigt hatten. Hier steht ja im Grunde `Odd (n^2) → Odd n`. Und unter
    Kontraposition ist das äquivalent zu `Even n → Even (n^2)`.

    **Du**: Richtig. Von hinten durch die Brust … Aber warte, im Moment steht da doch gar kein `→`.

    **Robo**: Erinner dich an `revert`. Mit `revert {h}` kannst du die Annahme `{h}` als
    Implikationsannahme ins Beweissziel schieben."
  -/
  Hint "Refer back to `even_square` as `Odd (n^2) → Odd n` is equivalent in contrapoition to `Even n → Even (n^2)`.
  Explain that lack of  `→` can be dealt with `revert` via `revert {h}` for `{h}`."
  revert h
  /-
  Hint "
    **Du**: Und jetzt kann ich dieses Kontrapositionslemma anwenden? Wie hieß das noch einmal?

    **Robo**: Tatsächlich kannst auch einfach `contrapose` schreiben."
  -/
  Hint "Apply contraposition lemma simply by `contrapose`"
  contrapose
  -- Hint (hidden := true) "**Robo**: Vielleicht hilft jetzt `not_odd_iff_even` weiter?"
  Hint (hidden := true) "`not_odd_iff_even` might help here"
  rw [not_odd_iff_even]
  rw [not_odd_iff_even]
  /-
  Hint "
    **Du**: Das sieht schon ganz gut aus. Jetzt kann ich tatsächlich das alte Lemma
    `even_square` anwenden!"
  -/
  Hint "Apply lemma `even_square`"
  apply even_square

NewTactic contrapose
DisabledTactic by_contra
TheoremTab "ℕ"

-- Conclusion "**Benedictus**: Hervorragend! Ich glaube, damit seid Ihr jetzt ganz gut gewappnet."
Conclusion "Conclusion Spinoza L05"
