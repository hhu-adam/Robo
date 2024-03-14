import Game.Metadata

World "Proposition"
Level 7

Title "Aus Falschem folgt vieles."

Introduction
"
Als nächstes kommen drei Querulanten. Der erste hat folgendes Problem:
"

Statement (A : Prop) (h : False) : A := by
  Hint "**Du** Wenn ich das jetzt richtig lese, ist `{A}` eine Aussage,
    und wir haben außerdem eine Annahme names `{h}`, die besagt …

    **Robo**: … die besagt, dass `False` gilt.

    **Du**: Ich dachte, `False` gilt nie?

    **Robo**: Ja, genau. Die Annahme ist `False`, also falsch.
    Und aus einer falschen Annahme kann man bekanntlich alles beweisen!
    Insbesondere die gesuchte Aussage `{A}`.

    **Du**: Und wie erkläre ich das jetzt diesem Formalosophen?

    **Robo**: Ich glaube, du musst ihn darauf hinweisen, dass zwischen der allgemeingültigen
    Annahme `True` und seiner Annahme `False` ein Widerspruch besteht. Probier mal `contradiction`."
  contradiction

Conclusion
"
Der erste Querulant ist offenbar zufrieden.

**Du**: War das jetzt ein Widerspruchsbeweis?

**Robo**: Nein, nein, ein Widerspruchsbeweis sieht anders aus. Das Argument hier war:
 wir haben eine `contradiction` in unserem Annahmen, also folgt jede beliebige Aussage.
"

/--
`contradiction` schliesst den Beweis wenn es einen Widerspruch in den Annahmen findet.

## Details
Ein Widerspruch in den Annahmen kann unter anderem folgendermassen aussehen:

* `(h : n ≠ n)`
* `(h : A)` und `(h' : ¬A)`
* `(h : False)` (i.e. ein Beweis von `False`)

## Beispiel

Folgenes Goal wird von `contradiction` bewiesen

## Hilfreiche Resultate

* Normalerweise wird `contradiction` gebraucht um einen Widerspruchsbeweis zu
  schliessen, der mit `by_contra` eröffnet wurde.
* Ein Beweis von `False` representiert in Lean einen Widerspruch.

```
Objekte:
  (n m : ℕ)
  (h : n = m)
  (g : n ≠ m)
Goal
  37 = 60
```
nach dem Motto \"ein Widerspruch beweist alles.\"
-/
TacticDoc contradiction

NewTactic contradiction
DisabledTactic tauto
