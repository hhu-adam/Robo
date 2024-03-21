import Game.Metadata

World "Function"
Level 4

Title "Injektivität"

Introduction
"
Ihr läuft durch verschiedenste Gänge der Bibliothek, allesamt mit Büchern entlang der Wände.

**Du**: Wenn wir wüssten, dass nur ein möglicher Weg hierhin führt, könnten wir
ausschliessen, dass wir im Kreis laufen.

Plötzlich begegnet ihr einem älteren Wesen mit Fakel. Auf die Frage antwortet es mit folgendem:
"
open Set Function

Statement :
    let f := fun (n : ℤ) ↦ n + 3
    Injective f := by
  Hint "
    **Robo**: `Injective` ist als `∀ \{a b : U}, f a = f b → a = b`
    definiert, also kannst du mit `intro` anfangen.

    **Du**: Und wenn ich das nicht weiss?

    **Robo**: Dann schaust du mit `unfold Injective` in die Definition rein."
  Branch
    unfold Injective
  intro a b
  Branch
    intro h
    Hint "**Robot**: Jetzt musst du wohl `{h}` vereinfachen."
    simp at h
    assumption
  Hint (hidden := true) "**Du**: Kann man das wohl vereinfachen?"
  Branch
    simp
  intro ha
  simp at ha
  assumption

NewDefinition Function.Injective
TheoremTab "Function"

Conclusion "**Du** Woa das war ja einfach!"
