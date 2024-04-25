import Game.Metadata

World "Cantor"
Level 1

Title "Cantor's Diagonalargument"

Introduction
"
**Cantor**: Wusstet ihr dass es keine surjektiven Funktionen `f : A → Set A` gibt? Faszinierend
oder? Wie das geht? Nehmt doch einmal die Menge `{ a | a ∉ f a }`. Wenn `f` surjektiv wäre,
welches `a : A` würde diese Menge als Bildpunkt haben?

[Tipp: `unfold_let` ist wie `unfold` und wird zukünftig in Lean zusammengeführt.
Brauche `unfold_let C` wenn eine lokale Definition in deinen Annahmen ist. Alternativ
funktionert auch `simp [C]`.]
"

Conclusion "**Du**: Uff. Aber erlich habe ich die das \"Diagonale\" daran noch nicht
ganz gesehen.


**Cantor**: Natürlich, das kann ich euch zeigen, aber da muss ich etwas ausholen…
"

open Set Function

Statement {A : Type*} :
    ∀ (f : A → Set A), ¬ Surjective f := by
  intro f
  Hint "**Du**: Also ein Widerspruchsbeweis?"
  by_contra hf
  Hint (strict := true) "**Robo**: Also wir sollen `let C := \{ a | a ∉ f a }` anschauen."
  let C := { a | a ∉ f a }
  Hint (strict := true)
  "**Du**: Und jetzt existiert durch Surjektivität ein Urbild von `{C}`.

  **Cantor**: Genau! Und dann überlegt euch, ob `y ∈ f y` ist oder nicht für
  dieses Urbild `y`!"
  have hsurj := hf C
  rcases hsurj with ⟨y, hy⟩
  by_cases y ∈ f y
  · Branch
      clear hf C hy
      Hint "**Du**: Jetzt will ich ja auch noch `y ∉ f y` zeigen für den Widerspruch.

      **Robo**: Dann sag doch `suffices hn : {y} ∉ {f} {y}`, erinnerst du dich?"
    suffices hn : y ∉ f y
    · contradiction
    rw [hy]
    rw [mem_setOf]
    simp
    assumption
  · suffices hn : y ∈ f y
    · contradiction
    rw [hy]
    rw [mem_setOf]
    assumption

NewTactic unfold_let -- TODO: remove
TheoremTab "Function"
