import Game.Metadata

World "Implis"
Level 4

Title "" -- "Implikation"

/-
Introduction
"
**Operationsleiter**: Das hier ist jetzt wieder ein lokales Problem.
"
-/
Introduction "`INTRO` Intro Implis L04"

Statement (A B C : Prop) (f : A → B) (g : B → C) : A → C := by
  /-
  Hint "
    **Du**: Ich soll Implikationen $A \\Rightarrow B \\Rightarrow C$ zu $A \\Rightarrow C$
    kombinieren?

    **Robo**: Vielleicht fängst du wieder mit `intro` an?"
  -/
  Hint "Try `intro`"
  intro h
  /-
  Hint "
    **Operationsleiter**: Also *ich* würde an dieser Stelle jetzt erst einmal
    `have hB : B` festhalten.

    **Robo**:  Für meinen Geschmack ein bisschen überflüssig.
    Aber gut, kann man machen.

    **Robo** *(zu dir)*: Los, probiers mal!
  "
  -/
  Hint "Try `have hB : B`"
  have hB : B := by
    /-
    Hint "
    **Robo**: Jetzt kannst du also erst einmal `B` beweisen …
  "
  -/
    Hint "Story"
    apply f
    assumption
  /-
  Hint "
    **Robo**: … und nachdem du das geschafft hast, hast du nun `{hB} : {B}` als
    Annahme zur Verfügung.
  "
  -/
  Hint "Story"
  apply g
  assumption

-- Conclusion "**Operationsleiter**: Ihr seid echt super!"
Conclusion "`CONC` Conclusion Implis L04"

NewTactic «have»  -- introduced here already so that Luna becomes independent of Spinoza
DisabledTactic tauto
