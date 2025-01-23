import Game.Metadata

World "Logo"
Level 11

Title "Und"

Introduction
"
Langsam wird die Schlange kürzer. Die nächste Formalosophin, ebenfalls häkelnd, hat folgendes Anliegen.
"

Statement (A B C : Prop) (h : A ∧ (B ∧ C)) : B := by
  Hint "
    **Du**: Jetzt müssen wir wohl die Annahme de-konstruieren.

    **Robo**: Ja, genau. Das geht am einfachsten mit `obtain ⟨h₁, h₂⟩ := {h}`.

    **Du**: Moment, wie schreib ich *das* denn hier auf?

    **Robo**: Die bleiden Klammern schreibst du als `\\<` und `\\>`, oder gleichzeitig als `\\<>`.
    Und h₁ schreibst du einfach als `h\\1`. Aber du kannst dir auch einfach andere Namen
    für `h₁` und `h₂`, zum Beispiel `obtain ⟨hA, hBC⟩ := {h}`."
  Branch
    obtain ⟨_h₁, _h₂⟩ := h
    Hint "**Robo**: Das sieht doch schon besser aus! Gleich nochmal!"
  obtain ⟨_h₁, g, _h₃⟩ := h
  Hint (hidden := true) "**Robo**: Du hast einen Beweis dafür in den *Annahmen*."
  assumption

Conclusion
"
**Robo**: Du hättest das übrigens auch direkt verschachtelt schreiben können:
`obtain ⟨h₁, h₂ , h₃⟩ := {h}`.
"

NewTactic obtain
DisabledTactic tauto
