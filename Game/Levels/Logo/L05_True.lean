import Game.Metadata

World "Logo"
Level 5

Title "" -- "True or False"

/-
Introduction
"
Der nächste Untertan in der Reihe ist ein Schelm.
"
-/
Introduction "`INTRO` Intro Logo L05"

Statement : True := by
  /-
  Hint "
    **Robo**: Dieses `True` ist eine spezielle Aussage, nämlich die Aussage, die immer und
    bedingungslos wahr ist.

    **Du**: Und was genau ist dann zu beweisen?

    **Robo**: Ich glaube, nichts. Probier mal `decide`."
  -/
  Hint "Try `decide`"
  decide

/-
Conclusion
"
**Schelm**: Wollte nur mal sehen, dass Ihr nicht auf den Kopf gefallen seid …

**Du** *(zu Robo)*: Können wir nicht einfach immer dieses `decide` verwenden?

**Robo**: Nein, `decide` funktioniert nur in speziellen Situationen, in denen es einen
einfachen Algorithmus gibt, der entscheidet, ob die Aussage wahr ist.
"
-/
Conclusion "Conclusion Logo L05: `decide` cannot be used every time. `decide` works only in special cases"

NewDefinition True False
NewTactic decide
DisabledTactic tauto
