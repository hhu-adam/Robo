import Game.Metadata

World "Implication"
Level 12

Title "by_cases"

Introduction
"
Beim nächsten Problem stutzt der Operationsleiter.

**Operationsleiter**: Ehrlich gesagt weiß ich gar nicht, wo dieses Blatt herkommt. Das ist
gar nicht von mir. Sieht aber irgendwie interessant aus.
"

Statement (A : Prop) : ¬A ∨ A := by
  Hint (strict := true) "
    **Du**: Naja, eine der beiden Aussagen `A` oder `¬A` wird schon wahr sein.

    **Robo**: Klarer Fall für eine Fallunterscheidung, würde ich sagen. Probier
    mal `by_cases h : A`."
  by_cases h : A
  Hint "
    **Robo**: Siehst du, jetzt hat der Beweis zwei Teile. Im ersten Teil nimmst
    du an, dass `A` wahr ist. Im zweiten nimmst du an, dass `A` falsch ist."
  right
  assumption
  left
  assumption

Conclusion
"
Der Operationsleiter nickt zustimmend.
"

NewTactic by_cases
DisabledTactic tauto
