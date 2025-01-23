import Game.Metadata

World "Logo"
Level 5

Title "True or False"

Introduction
"
Der nächste Untertan in der Reihe ist ein Schelm.
"

Statement : True := by
  Hint "
    **Robo**: Dieses `True` ist eine spezielle Aussage, nämlich die Aussage, die immer und
    bedingungslos wahr ist.

    **Du**: Und was genau ist dann zu beweisen?

    **Robo**: Ich glaube, nichts. Probier mal `decide`."
  decide

Conclusion
"
**Schelm**: Wollte nur mal sehen, dass Ihr nicht auf den Kopf gefallen seid …

**Du** *(zu Robo)*: Können wir nicht einfach immer dieses `decide` verwenden?

**Robo**: Nein, `decide` funktioniert nur in speziellen Situationen, in denen es einen
einfachen Algorithmus gibt, der entscheidet, ob die Aussage wahr ist.
"

NewDefinition True
NewTactic decide
DisabledTactic tauto
