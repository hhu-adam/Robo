import Game.Metadata

World "Implication"
Level 4

Title "Implikation"

Introduction
"
**Operationsleiter**: Das hier ist jetzt wieder ein lokales Problem.
"

Statement (A B C : Prop) (f : A → B) (g : B → C) : A → C := by
  Hint "
    **Du**: Ich soll Implikationen $A \\Rightarrow B \\Rightarrow C$ zu $A \\Rightarrow C$
    kombinieren?

    **Robo**: Vielleicht fängst du wieder mit `intro` an?"
  intro h
  Hint (hidden := true) "**Robo**: Das ist wieder eine Anwendung von `apply`."
  Branch
    apply g
    apply f
    assumption
  apply f at h
  apply g at h
  assumption

Conclusion "**Operationsleiter**: Ihr seid echt super!"

DisabledTactic tauto
