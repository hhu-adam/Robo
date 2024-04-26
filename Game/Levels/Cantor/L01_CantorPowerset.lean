import Game.Metadata

World "Cantor"
Level 1

Title "Cantor's Diagonalargument"

Introduction
"
**Cantor**: Wusstet ihr dass es keine surjektiven Funktionen `f : A → Set A` gibt? Faszinierend
oder? Wie das geht? Nehmt doch einmal die Menge `C := { a | a ∉ f a }`. Wenn `f` surjektiv wäre,
welches `a : A` würde diese Menge als Bildpunkt haben? Hier, ich gebe euch einfach `C` auch
schon mit!

[Tipp: `unfold_let` ist wie `unfold` und wird zukünftig in Lean zusammengeführt.
Brauche `unfold_let C` wenn eine lokale Definition in deinen Annahmen ist. Alternativ
funktionert auch `simp [C]`.]
"

Conclusion "**Du**: Uff. Aber ehrlich habe ich die das \"Diagonale\" daran noch nicht
ganz gesehen.


**Cantor**: Natürlich, das kann ich euch zeigen, aber da muss ich etwas ausholen…
"

open Set Function

Statement {A : Type*} (f : A → Set A) :
    let C := { a | a ∉ f a }
    ¬ Surjective f := by
  Hint (hidden := true) "**Du**: Also ein Widerspruchsbeweis?"
  by_contra hf
  Hint (strict := true)
  "**Du**: Und jetzt existiert durch Surjektivität ein Urbild von `{C}`.

  **Cantor**: Genau! Und dann überlegt euch, ob `b ∈ f b` ist oder nicht für
  dieses Urbild `b`!"
  have hsurj := hf C
  rcases hsurj with ⟨b, hb⟩
  Hint (hidden := true) "**Robo**: Das machen wir glaubs am besten mit `by_cases`."
  by_cases b ∈ f b
  · Branch
      clear hf C hb
      Hint "**Du**: Jetzt will ich ja auch noch `{b} ∉ {f} {b}` zeigen für den Widerspruch.

      **Robo**: Dann sag doch `suffices hn : {b} ∉ {f} {b}`, erinnerst du dich?"
    suffices hn : b ∉ f b
    · contradiction
    rw [hb]
    rw [mem_setOf]
    simp
    assumption
  · Hint "**Robo**: Und noch den Fall wenn `{b} ∉ {f} {b}`"
    suffices hn : b ∈ f b
    · contradiction
    rw [hb]
    rw [mem_setOf]
    assumption

NewTactic unfold_let -- TODO: remove
TheoremTab "Function"
