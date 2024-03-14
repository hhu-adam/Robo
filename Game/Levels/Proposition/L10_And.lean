import Game.Metadata

World "Proposition"
Level 11

Title "Und"

Introduction
"
Langsam wird die Schlange kürzer. Die nächste Formalosophin, ebenfalls häkelnd, hat folgendes Anliegen.
"

Statement (A B C : Prop) (h : A ∧ (B ∧ C)) : B := by
  Hint "
    **Du**:  Jetzt müssen wir wohl die Annahme de-konstruieren.

    **Robo**: Ja, genau. Das geht am einfachsten mit `rcases {h} with ⟨h₁, h₂⟩`.

    **Du**: Moment, wie schreib ich *das* denn hier auf?

    **Robo**: Die bleiden Klammern schreibst du als `\\<` und `\\>`, oder gleichzeitig als `\\<>`.
    Und h₁ schreibst du einfach als `h\\1`. Aber du kannst dir auch einfach andere Namen
    für `h₁` und `h₂`, zum Beispiel `rcases {h} with ⟨hA, hBC⟩`"
  Branch
    rcases h with ⟨h₁, h₂⟩
    Hint "**Robo**: Das sieht doch schon besser aus!  Gleich nochmal!"
  rcases h with ⟨_, ⟨g , _⟩⟩
  Hint (hidden := true) "**Robo**: Du hast einen Beweis dafür in den *Annahmen*."
  assumption

Conclusion
"
**Robo**: Du hättest das übrigens auch direkt verschachtelt schreiben können:
`rcases h with ⟨h₁, ⟨h₂ , h₃⟩⟩`.
"

/--
`rcases h` teilt eine Annahme `h` in ihre Einzelteile auf.

## Details
Für Annahmen die Strukturen sind, wie z.B. `h : A ∧ B` (oder `∃x, P x`) kann man die
Einzelteile mit  `rcases h with ⟨a, b⟩` (oder `rcases h with ⟨x, hx⟩`) benennen.

Für eine Annahme der Form `h : A ∨ B` kann man mit `rcases h with ha | hb` zwei Goals
erzeugen, einmal unter Annahme der linken Seite, einmal unter Annahme der Rechten.

## Hilfreiche Resultate

* Für `n : ℕ` hat `rcases n` einen ähnlichen Effekt wie `induction n` mit dem Unterschied,
  dass im Fall `n + 1` keine Induktionshypothese zur Verfügung steht.
* In Lean gibt es auch die Taktik `cases`, die gleich funktioniert wie `rcases` aber
  einen mehrzeiligen Syntax hat:
  ```
  cases h with
  | inl ha =>
    sorry
  | inr hb =>
    sorry
  ```
  Hier sind `inl`/`inr` die Namen der Fälle und `ha`/`hb` sind frei gewählte Namen für die
  freien Variablen
-/
TacticDoc rcases

NewTactic rcases
DisabledTactic tauto
