import Game.Metadata

World "Implis"
Level 7

Title "" -- "Genau dann, wenn"

/-
Introduction
"
**Operationsleiter**: Hier ist noch so etwas.
"
-/
Introduction "Intro Implis L07"

Statement (A B : Prop) (h : A ↔ B) : B ↔ A := by
  /-
  Hint "
    **Du**: Das ist ja nur verdreht.

    **Robo**: Ich kenne ein Werkzeug dafür. Mit `symm` oder `symm at {h}` kannst du eines
    der beiden umdrehen."
  -/
  Hint "Try `symm` or `symm at {h}` to turn one around"
  Branch
    symm at h
    assumption
  symm
  assumption

/-
Conclusion
"
**Operationsleiter**: Das war ja symmpel. Das nächste Problem sieht aber schwieriger aus.
"
-/
Conclusion "Conclusion Implis L07"

NewTactic symm
DisabledTactic tauto
