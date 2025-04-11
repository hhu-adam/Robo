import Game.Metadata

World "Logo"
Level 4

Title "" -- "Logische Aussagen"

Introduction
"
Ein dritter Untertan kommt mit folgendem Problem.
"

Statement (A : Prop) (hA : A) : A := by
  Hint "
    **Robo**: Hier bedeutet `{A} : Prop` wieder, dass `{A}` irgendeine Aussage ist.
      Und `{hA}` ist ein Name für die Annahme, dass `{A}` wahr ist.

    **Du**: Und unter dieser Annahme sollen wir jetzt `{A}` beweisen?

    **Robo**: Ja. Da kommst du jetzt selbst drauf, wie das geht, oder?"
  Hint (hidden := true) "**Robo**: Ist doch genau wie eben:
    die Aussage, die zu beweisen ist, gehört selbst zu den Annahmen.
    Also wird `assumption` auch wieder funktionieren."
  assumption

Conclusion "**Untertan**: Das ging ja schnell. Super! Vielen Dank."

DisabledTactic tauto
