import Game.Metadata

World "Implis"
Level 8

Title "" -- "Genau dann, wenn"

/-
Introduction
"
**Operationsleiter**: Hier, könnt ihr dazu auch was sagen?
"
-/
Introduction "`INTRO` Intro Implis L08"

Statement (A B C D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C := by
  /-
  Hint "
    **Du**: $B \\iff A \\iff D \\iff C$, die sind doch alle äquivalent…

    **Robo**: Ja, aber du musst ihm helfen, die Äquivalenzen umzuschreiben. Mit `rw [h₁]` kannst
    du `C` durch `D` ersetzen."
  -/
  Hint "Rewrite $B \\iff A \\iff D \\iff C$. Start with `rw [h₁]` to replace `C` with `D`"
  rw [h₁]
  /-
  Hint "
    **Du** Und wenn ich in die andere Richtung umschreiben möchte?

    **Robo**: Dann schreibst du ein `←` (`\\l`, also klein \"L\") vor den Namen, also `rw [← hₓ]`."
  -/
  Hint "To rewrite into the other direction you can use `←` (`\\l`) infront of the name. Try `rw [← hₓ]`"
  Branch
    rw [← h₃]
    /-
    Hint "
      **Du**: Ehm, das war verkehrt.

      **Robo**: Ja, anders herum wär's besser gewesen. Aber wenn du jetzt einfach weitermachst,
      bis Du sowas wie `A ↔ A` erhältst, kann `rfl` das beweisen.

      **Robo: Da fällt mir ein, `rw` wendet ohnehin auch versuchsweise `rfl` an.
      Das heißt, du musst `rfl` nicht einmal ausschreiben."
    -/
    Hint "You can continue until there is `A ↔ A` and then apply `rfl`. `rw` always uses `rfl`,
    meaning hat `rfl` does not have to be written"
    rw [h₂]
  rw [←h₂]
  assumption

/-
Conclusion
"
**Operationsleiter**: Wenn Ihr so weitermacht, dann kommen wir ja durch den ganzen Packen durch!
"
-/
Conclusion "`CONC` Conclusion Implis L08"

NewTactic rw
NewHiddenTactic nth_rw
DisabledTactic tauto
