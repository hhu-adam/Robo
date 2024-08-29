import Game.Metadata

World "Implication"
Level 7

Title "Genau dann, wenn"

Introduction
"
**Operationsleiter**: Hier ist noch so etwas.
"

Statement (A B : Prop) (h : A ↔ B) : B ↔ A := by
  Hint "
    **Du**: Das ist ja nur verdreht.

    **Robo**: Ich kenne ein Werkzeug dafür. Mit `symm` oder `symm at {h}` kannst du eines
    der beiden umdrehen."
  Branch
    symm at h
    assumption
  symm
  assumption

Conclusion
"
**Operationsleiter**: Das war ja symmpel. Das nächste Problem sieht aber schwieriger aus.
"

NewTactic symm
DisabledTactic tauto
