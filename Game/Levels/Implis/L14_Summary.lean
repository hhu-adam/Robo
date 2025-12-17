import Game.Metadata

World "Implis"
Level 14

Title "" -- "Zusammenfassung"

/-
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

|     | Beschreibung                 |
|:--- |:---------------------------- |
| `→` | Implikation                  |
| `↔` | genau-dann-wenn / Äquivalenz |

## Taktiken

| Taktik           | Beispiel                                                          |
|:---------------- |:----------------------------------------------------------------- |
| `intro`          | holt linke Seite einer Implikations im Beweisziel in die Annahmen |
| `revert`         | Umkehrung von `intro`                                             |
| `apply`          | wendet Implikation “rückwärts” auf das Beweisziel an              |
| `apply at`       | wendet Implikation “vorwärts” auf eine Annahme an                 |
| `symm`           | ändert `A ↔ B` zu `B ↔ A`                                         |
| `trans`          | ändert `A ↔ C` zu `A ↔ B` und `B ↔ C`                             |
| `rw [h] `        | schreibt Beweisziel mithilfe der Äquivalenz `h` um                |
| `rw [h] at h₁`   | schreibt Annahme `h₁` mithilfe der Äquivalenz `h` um              |
| `by_cases h : P` | Fallunterscheidung zwischen `P` und `¬P`                          |
"
-/
Introduction "
Intro Implis L14: This chapter used the following operations:
`→`, `↔`, `intro`, `revert` (reversal of `intro`), `apply`, `apply at`, `symm` (changes `A ↔ B` to `B ↔ A`),
`trans` (changes `A ↔ C` to `A ↔ B` and `B ↔ C`), `rw [h] ` (rewrite goal with `h`), `rw [h] at h₁` (rewrite
assumption `h₁` using `h`) and `by_cases h : P` (introduce cases `P` and `¬P`)
"

/-- This kind of logical expression can often be solved via `tauto`. -/
TheoremDoc imp_iff_or_not as "imp_if_or_not" in "Logic"

/-- In most cases `tauto` can be used to solve this kind of logical expression. -/
TheoremDoc imp_iff_not_or as "imp_iff_not_or" in "Logic"

set_option tactic.hygienic false

Statement imp_iff_not_or {A B : Prop} : (A → B) ↔ ¬ A ∨ B := by
  /-
  Hint "**Du** *(flüsternd)*: Ist das nicht die Definition von `→`?

  **Robo** *(flüsternd)*: Könnte man so sehen. Aber auf Leansch ist das bloß eine Äquivalenz."
  -/
  Hint "Remind that `→` in this case is equivalence"
  constructor
  intro h
  -- Hint (hidden := true) "**Robo**: Vielleicht kannst du wieder `by_cases` benutzen."
  Hint (hidden := true) "Maybe try `by_cases` again"
  Branch
    by_cases A


  by_cases hA : A
  apply h at hA
  right
  assumption
  left
  assumption
  -- Hint (hidden := true) "**Robo**: Na Implikationen gehst du immer mit `intro` an."
  Hint (hidden := true) "Try `intro` to solve implication"
  intro h
  intro ha
  Branch
    by_cases ha : A
  Branch
    by_cases A
  -- Hint (hidden := true) "**Robo**: Ich würde mal die Annahme `h` mit `obtain` aufteilen."
  Hint (hidden := true) "To divide assumption `h` use `obtain`"
  obtain h | h :=  h
  contradiction
  assumption

DisabledTactic tauto

NewTheorem imp_iff_or_not

/-
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
-/
Conclusion "Conclusion Implis L14"
