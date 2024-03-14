import Game.Metadata

World "Implication"
Level 7

Title "Genau dann, wenn"

Introduction
"
**Operationsleiter**: Hier ist noch so etwas.
"

Statement (A B C D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C := by
  Hint "
    **Du**: $B \\iff A \\iff D \\iff C$, die sind doch alle äquivalent…

    **Robo**: Ja, aber du musst ihm helfen, die Äquivalenzen umzuschreiben. Mit `rw [h₁]` kannst
    du `C` durch `D` ersetzen."
  rw [h₁]
  Hint "
    **Du** Und wenn ich in die andere Richtung umschreiben möchte?

    **Robo**: Dann schreibst du ein `←` (`\\l`, also klein \"L\") vor den Namen, also `rw [← hₓ]`."
  Branch
    rw [← h₃]
    Hint "
      **Du**: Ehm, das war verkehrt.

      **Robo**: Ja, anders herum wär's besser gewesen. Aber wenn du jetzt einfach weitermachst,
      bis Du sowas wie `A ↔ A` erhältst, kann `rfl` das beweisen.

      **Robo: Da fällt mir ein, `rw` wendet ohnehin auch versuchsweise `rfl` an.
      Das heißt, du musst `rfl` nicht einmal ausschreiben."
    rw [h₂]
  rw [←h₂]
  assumption

Conclusion
"
**Operationsleiter**:  Wenn Ihr so weitermacht, dann kommen wir ja durch den ganzen Packen durch!
"

/--
Wenn man eine Annahme `(h : X = Y)` hat, kann man mit
`rw [h]` alle `X` im Goal durch `Y` ersetzen.

## Details

* `rw [←h]` wendet `h` rückwärts an und ersetzt alle `Y` durch `X`.
* `rw [h, g, ←f]`: Man kann auch mehrere `rw` zusammenfassen.
* `rw [h] at h₂` ersetzt alle `X` in `h₂` zu `Y` (anstatt im Goal).

`rw` funktioniert gleichermassen mit Annahmen `(h : X = Y)` also auch
mit Theoremen/Lemmas der Form `X = Y`
-/
TacticDoc rw

NewTactic rw
DisabledTactic tauto
