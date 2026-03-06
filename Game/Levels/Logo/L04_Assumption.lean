import Game.Metadata

World "Logo"
Level 4

Title "" -- "Logische Aussagen"

/-
Introduction
"
Ein dritter Untertan kommt mit folgendem Problem.
"
-/
Introduction "Intro Logo L04"

Statement (A : Prop) (hA : A) : A := by
  /-
  Hint "
    **Robo**: Hier bedeutet `{A} : Prop` wieder, dass `{A}` irgendeine Aussage ist.
      Und `{hA}` ist ein Name für die Annahme, dass `{A}` wahr ist.

    **Du**: Und unter dieser Annahme sollen wir jetzt `{A}` beweisen?

    **Robo**: Ja. Da kommst du jetzt selbst drauf, wie das geht, oder?"
  -/
  Hint "Explain that `{A} : Prop` means that `{A}` is some statement.
  `{hA}` is the name of the assumption that `{A}` is true. Try to solve `{A}` using said assumption"
  /-
  Hint (hidden := true) "**Robo**: Ist doch genau wie eben:
    die Aussage, die zu beweisen ist, gehört selbst zu den Annahmen.
    Also wird `assumption` auch wieder funktionieren."
  -/
  Hint (hidden := true) "Use `assumption` as goal is in assumptions"
  assumption

/-
Conclusion "**Untertan**: Das ging ja schnell. Super! Vielen Dank."
-/
Conclusion "Conclusion Logo L04"

DisabledTactic tauto
