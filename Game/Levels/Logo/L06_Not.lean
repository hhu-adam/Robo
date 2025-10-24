import Game.Metadata

World "Logo"
Level 6

Title "" -- "Not"

/-
Introduction
"
Der Schelm hat noch eine Schwester dabei.
"
-/
Introduction "`INTRO` Intro Logo L06"

Statement : ¬False := by
  /-
  Hint "
    **Robo**: Dieses Zeichen `¬` bedeutet Negation. Also wenn eine Aussage `(A : Prop)`
    wahr ist, dann ist `¬A` falsch, und umgekehrt.

    **Du**: Und `False` ist wahrscheinlich die Aussage, die immer falsch ist?

    **Robo**: Ja, richtig.

    **Du**: Ist das jetzt nicht doch wieder `decide`?

    **Robo**: Probier mal!"
  -/
  Hint "Try `decide`"
  decide

/-
Conclusion
"
Die Schwester lacht und eilt ihrem Bruder hinterher.
"
-/
Conclusion "`CONC` Conclusion Logo L06"

NewDefinition False Not
DisabledTactic tauto
