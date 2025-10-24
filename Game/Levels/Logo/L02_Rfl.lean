import Game.Metadata

World "Logo"
Level 2

Title "" -- "Aller Anfang ist… ein Einzeiler?"

/-
Introduction
"
In der Zwischenzeit hat bereits sich eine lange Schlange Untertanen gebildet, die gern ihren
Fragen stellen würden. Logisinde winkt den ersten nach vorn. Er räuspert sich.

**Untertan**: Warum ist $42 = 42$?

Du schaust ihn fassungslos an.
Er schreibt es dir wieder auf.
"
-/
Introduction "Intro Logo L02: Why is $42 = 42$?"

Statement :
  42 = 42 := by
  /-
  Hint "**Robo**: Ist doch klar. Du musst ihn einfach daran erinnern,
    dass Gleichheit *reflexiv* ist. Probier mal `rfl`."
  -/
  Hint "Try `rfl`"
  rfl

/-
Conclusion
"
**Untertan**: Ah, richtig. Ja, Sie haben ja so recht. Das vergesse ich immer. Rfl, rfl, rfl …
"
-/
Conclusion "`CONC` Conclusion Logo L02"

NewDefinition Eq

NewTactic rfl
DisabledTactic tauto
