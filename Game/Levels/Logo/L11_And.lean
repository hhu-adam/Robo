import Game.Metadata

World "Logo"
Level 11

Title "" -- "Und"

/-
Introduction
"
Langsam wird die Schlange kürzer. Die nächste Formalosophin, ebenfalls häkelnd, hat folgendes Anliegen.
"
-/
Introduction "Intro Logo L11"

Statement (A B C : Prop) (h : A ∧ (B ∧ C)) : B := by
  /-
  Hint "
    **Du**: Jetzt müssen wir wohl die Annahme de-konstruieren.

    **Robo**: Ja, genau. Das geht am einfachsten mit `obtain ⟨h₁, h₂⟩ := {h}`.

    **Du**: Moment, wie schreib ich *das* denn hier auf?

    **Robo**: Die bleiden Klammern schreibst du als `\\<` und `\\>`, oder gleichzeitig als `\\<>`.
    Und h₁ schreibst du einfach als `h\\1`. Aber du kannst dir auch einfach andere Namen
    für `h₁` und `h₂`, zum Beispiel `obtain ⟨hA, hBC⟩ := {h}`."
  -/
  Hint "Deconstruct assumption by `obtain ⟨h₁, h₂⟩ := {h}`. The brackets can be written seperatly
  as `\\<` and `\\>` or simultaneously as `\\<>`. The first assumption can be named `h\\1`. Other names
  than `h₁` und `h₂` can be chosen as well e.g. `obtain ⟨hA, hBC⟩ := {h}`"
  Branch
    obtain ⟨_h₁, _h₂⟩ := h
    -- Hint "**Robo**: Das sieht doch schon besser aus! Gleich nochmal!"
    Hint "Try obtain tactic"
  obtain ⟨_h₁, g, _h₃⟩ := h
  -- Hint (hidden := true) "**Robo**: Du hast einen Beweis dafür in den *Annahmen*."
  Hint "Try Assumption tactic"
  assumption

/-
Conclusion
"
**Robo**: Du hättest das übrigens auch direkt verschachtelt schreiben können:
`obtain ⟨h₁, h₂ , h₃⟩ := h`.
"
-/
Conclusion "Conclusion Logo L11: Could have been written as `obtain ⟨h₁, h₂ , h₃⟩ := h`"

NewTactic obtain
DisabledTactic tauto
