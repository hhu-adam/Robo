import Game.Metadata

World "Proposition"
Level 2

Title "Aller Anfang ist... ein Einzeiler?"

Introduction
"
In der Zwischenzeit hat bereits sich eine lange Schlange Untertanen gebildet, die gern ihren
Fragen stellen würden. Logisinde winkt den ersten nach vorn. Er räuspert sich.

**Untertan**: Warum ist $42 = 42$?

Du schaust ihn fassungslos an.
Er schreibt es dir wieder auf.
"

Statement :
  42 = 42 := by
  Hint "**Robo**: Ist doch klar.  Du musst ihn einfach daran erinnern,
    dass Gleichheit *reflexiv* ist. Probier mal `rfl`."
  rfl

Conclusion
"
**Untertan**: Ah, richtig. Ja, Sie haben ja so recht.  Das vergesse ich immer.  Rfl, rfl, rfl …
"

/--
`rfl` beweist ein Goal der Form `X = X`.

## Detail

`rfl` beweist jedes Goal `A = B` wenn `A` und `B` per Definition das gleiche sind (DefEq).
Andere Taktiken rufen `rfl` oft am Ende versteckt
automatisch auf um zu versuchen, den Beweis zu schliessen.


## Beispiel
`rfl` kann folgende Goals beweisen:

```
Objekte
  a b c : ℕ
Goal:
  (a + b) * c = (a + b) * c
```

```
Objekte
  n : ℕ
Goal
  1 + 1 = 2
```
denn Lean liest dies intern als `0.succ.succ = 0.succ.succ`.
-/
TacticDoc rfl

NewTactic rfl
DisabledTactic tauto
