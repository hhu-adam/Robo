import Game.Metadata

World "Implis"
Level 14

Title "" -- "Zusammenfassung"

Introduction
"
**Operationsleiter**: Ihr habt mir wirklich so geholfen! Hier ist das letzte Problem.
Das habe ich von meinem Vorgänger geerbt. Er hat behauptet, wenn wir das lösen können,
dann läuft hier wieder alles. Aber es sah mir immer viel zu schwierig aus, um es überhaupt
zu versuchen. Wollt Ihr es einmal probieren?

**Du**: Klar, zeig her! Robo, kannst du mir vielleicht auch noch einmal so eine nette
Zusammenfassung anzeigen, was ich theoretisch in den letzten fünf Minuten gelernt habe?

**Robo**: Hier ist die Übersicht:

## Notationen / Begriffe

|               | Beschreibung                                             |
|:--------------|:---------------------------------------------------------|
| →             | Eine Implikation.                                        |
| ↔             | Genau-dann-wenn / Äquivalenz.                            |

## Taktiken

|     | Taktik                    | Beispiel                                                   |
|:----|:--------------------------|:-----------------------------------------------------------|
| 8   | `intro`                   | Für eine Implikation im Goal.                              |
| 9   | `revert`                  | Umkehrung von `intro`.                                     |
| 10  | `apply`                   | Wendet Implikation/Theorem (rückwärts) auf das Goal an.    |
| 10ᵇ | `apply at`                | Wendet Implikation/Theorem (forwärts) auf eine Annahme an. |
| 11  | `symm`                    | Tauscht `A ↔ B` zu `B ↔ A`.                                |
| 12  | `trans`                   | Ändert `A ↔ C` zu `A ↔ B` und `B ↔ C`                      |
| 13  | `rw`                      | Umschreiben zweier äquivalenter Aussagen.                  |
| 13ᵇ | `rw`                      | Benutzt ein Lemma, dessen Aussage eine Äquivalenz ist.     |
| 14  | `by_cases`                | Fallunterscheidung `P` und `¬P`                            |
"

set_option tactic.hygienic false

Statement imp_iff_not_or {A B : Prop} : (A → B) ↔ ¬ A ∨ B := by
  Hint "**Du** *(flüsternd)*: Ist das nicht die Definition von `→`?

  **Robo** *(flüsternd)*: Könnte man so sehen. Aber auf Leansch ist das bloß eine Äquivalenz."
  constructor
  intro h
  Hint (hidden := true) "**Robo**: Vielleicht kannst du wieder `by_cases` benutzen."
  Branch
    by_cases A


  by_cases hA : A
  apply h at hA
  right
  assumption
  left
  assumption
  Hint (hidden := true) "**Robo**: Na Implikationen gehst du immer mit `intro` an."
  intro h
  intro ha
  Branch
    by_cases ha : A
  Branch
    by_cases A
  Hint (hidden := true) "**Robo**: Ich würde mal die Annahme `h` mit `obtain` aufteilen."
  obtain h | h :=  h
  contradiction
  assumption

DisabledTactic tauto

/---/
TheoremDoc imp_iff_or_not as "imp_if_or_not" in "Logic"
NewTheorem imp_iff_or_not

Conclusion "
**Operationsleiter**: Das ist ja fantastisch! Tausend Dank! Dann will ich Euch auch gar
nicht länger aufhalten.
Ihr wollt bestimmt weiter zum Planeten Quantus, oder?

**Du**: Ehm, vielleicht …

**Operationsleiter**: Dann habe ich noch eine letzte Bitte. Ich habe hier noch ein Päckchen
für die Königin von Quantus! Auch schon von meinem Vorgänger geerbt. Die Post will es
nicht annehmen, weil ich die Adresse nicht weiß. Könntet Ihr es vielleicht zu ihr mitnehmen?

**Du**: Klar! Robo, halt mal.

Robo nimmt das Päckchen und lässt es irgendwo in seinem Innern verschwinden.
Der Operationsleiter sieht ihn entgeistert an.

**Robo**: Keine Angst, ich verdaue nichts!
"
