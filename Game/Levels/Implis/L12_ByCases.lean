import Game.Metadata

World "Implis"
Level 12

Title "" -- "by_cases"

/-
Introduction
"
Beim nächsten Problem stutzt der Operationsleiter.

**Operationsleiter**: Ehrlich gesagt weiß ich gar nicht, wo dieses Blatt herkommt. Das ist
gar nicht von mir. Sieht aber irgendwie interessant aus.
"
-/
Introduction "Intro Implis L12"

Statement (A : Prop) : ¬A ∨ A := by
  /-
  Hint (strict := true) "
    **Du**: Naja, eine der beiden Aussagen `A` oder `¬A` wird schon wahr sein.

    **Robo**: Klarer Fall für eine Fallunterscheidung, würde ich sagen. Probier
    mal `by_cases h : A`."
  -/
  Hint "Either `A` or `¬A` is true. Try `by_cases h : A`"
  by_cases h : A
  /-
  Hint "
    **Robo**: Siehst du, jetzt hat der Beweis zwei Teile. Im ersten Teil nimmst
    du an, dass `A` wahr ist. Im zweiten nimmst du an, dass `A` falsch ist."
  -/
  Hint "Proof consists now of two parts. First assumes that `A` is true. Second assumes that `A`
  is false"
  right
  assumption
  left
  assumption

/-
Conclusion
"
Der Operationsleiter nickt zustimmend.
"
-/
Conclusion "Conclusion Implis L12"

NewTactic by_cases
DisabledTactic tauto
