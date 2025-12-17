import Game.Metadata

World "Logo"
Level 7

Title "" -- "Aus Falschem folgt vieles."

/-
Introduction
"
Als nächstes kommen drei Querulanten. Der erste hat folgendes Problem:
"
-/
Introduction "Intro Logo L07"

Statement (A : Prop) (h : False) : A := by
  /-
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
  -/
  Hint "Explain that `{A}` is a statement and `{h}` is the assumption that `False` is true.
   Remind that `False` is always false. Explain that assumption `False` is false. As any statement
   `{A}` can be proven from a false assumption. Point out contradiction between `True` and `False`
   by applying `contradiction`."
  contradiction

/-
Conclusion
"
Der erste Querulant ist offenbar zufrieden.

**Du**: War das jetzt ein Widerspruchsbeweis?

**Robo**: Nein, nein, ein Widerspruchsbeweis sieht anders aus. Das Argument hier war:
 wir haben eine `contradiction` in unserem Annahmen, also folgt jede beliebige Aussage.
"
-/
Conclusion "Conclusion Logo L07: There is `contradiction` in assumptions"

NewTactic contradiction
DisabledTactic tauto
