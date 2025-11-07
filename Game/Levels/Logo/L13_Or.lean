import Game.Metadata

World "Logo"
Level 13

Title "" -- "Oder"

/-
Introduction
"
Der nächste bitte …
"
-/
Introduction "`INTRO` Intro Logo L12/L13"

/--  -/
Statement (A B : Prop) (h : (A ∧ B) ∨ A) : A := by
  /-
  Hint "**Robo** Schau mal, wenn du mit dem Finger eine Annahme berührst, zeigt es dir,
wie die Klammern gesetzt sind. Irre…

**Du** Ah ich sehe, also `({A} ∧ {B}) ∨ {A}`!

**Du** Ich glaube den ganzen Zircus hier langsam nicht mehr:
Zuerst ein \"Und\" im Ziel, dann \"Und\" in der Annahme, dann \"Oder\" im Ziel und jetzt
\"Oder\" in der Annahme, die haben sich doch abgesprochen!

**Robo** Lass ihnen doch ihren Spaß.
Wir sind ja gleich hier fertig, und können zu einem interessanteren Planeten weiterfliegen.

**Du** Also, wieder `obtain …`?

**Robo** Ja, aber diesmal nicht `obtain ⟨h₁, h₂⟩ := {h}`, sondern `obtain h | h := {h}`."
-/
  Hint "Observe goal as `({A} ∧ {B}) ∨ {A}`.
  Do not try `obtain …` as `obtain ⟨h₁, h₂⟩ := {h}` but as `obtain h | h := {h}`"
  obtain h | h := h
  /-
  · Hint "**Robo**
    Jetzt musst du dein Ziel zweimal beweisen:
    Einmal unter Annahme der linken Seite `{A} ∧ {B}`,
    und einmal unter Annahme der rechten Seite `{A}`.
    Hier haben nehmen wir an, die linke Seite
    sei wahr."
  -/
  · Hint "Prove goal once for `{A} ∧ {B}` and once for `{A}`"
    /-
    Hint (hidden := true) " **Robo** Wie man mit einem Und in den Annahmen umgeht,
    weißt du doch schon:
    `obtain ⟨h₁, h₂⟩ := {h}`. Zur Erinnerung: Für die Klammern schreibst du `\\<>`."
    -/
    Hint (hidden := true) "Try `obtain ⟨h₁, h₂⟩ := {h}`. Write brackets as `\\<>`"
    obtain ⟨h₁, _h₂⟩ := h
    assumption
  /-
  · Hint (strict := true) "**Robo** Jetzt musst du dein Ziel noch unter der rechten Annahme
    von `({A} ∧ {B}) ∨ {A}` zeigen, also angenommen, `{A}` sei wahr."
  -/
  · Hint (strict := true) "Show goal via `({A} ∧ {B}) ∨ {A}` i.e. assume `{A}` is true"
    assumption

/-
Conclusion
"**Du** Okay, das scheint ihn zufriedenzustellen. Nur noch eine Seele…
Kannst du mir vorher noch einmal kurz alles Leansch zusammenfassen,
das du mir bis hierher beigebracht hast?

Robo strahlt überglücklich. Noch *nie* warst du so auf ihn angewiesen.

**Robo** Na klar, schau her!

## Notationen / Begriffe

|               | Beschreibung                                                             |
|:--------------|:-------------------------------------------------------------------------|
| *Goal*        | Was aktuell zu beweisen ist.                                             |
| *Annahme*     | Objekte & Resultate, die man zur Verfügung hat.                          |
| *Taktik*      | Befehl im Beweis. Entspricht einem Beweisschritt.                        |
| `ℕ`           | Typ aller natürlichen Zahlen.                                            |
| `0, 1, 2, …`  | Explizite natürliche Zahlen.                                             |
| `=`           | Gleichheit.                                                              |
| `≠`           | Ungleichheit. Abkürzung für `¬(·=·)`.                                    |
| `Prop`        | Typ aller logischen Aussagen.                                            |
| `True`        | Die logische Aussage `(True : Prop)` ist bedingungslos wahr.             |
| `False`       | Die logische Aussage `(False : Prop)` ist bedingungslos falsch.          |
| `¬`           | Logische Negierung.                                                      |
| `∧`           | Logisch UND.                                                             |
| `∨`           | Logisch ODER.                                                            |
| `(n : ℕ)`     | Eine natürliche Zahl.                                                    |
| `(A : Prop)`  | Eine logische Aussage.                                                   |
| `(ha : A)`    | Ein Beweis, dass die logische Aussage `(A : Prop)` wahr ist.             |
| `(h : A ∧ B)` | Eine Annahme, die den Namen `h` bekommen hat.                            |


## Taktiken

Die Worte, die du aktiv gebrauchen musst, heißen zusammengefasst `Taktiken`.
Hier sind alle Taktiken, die wir auf diesem Planeten gebraucht haben:

|    | Taktik                    | Beispiel                                           |
|:---|:--------------------------|:---------------------------------------------------|
| 1  | `rfl`                     | Beweist `A = A`.                                   |
| 2  | `assumption`              | Sucht das Goal in den Annahmen.                    |
| 3  | `contradiction`           | Sucht einen Widerspruch.                           |
| 4  | `decide`                  | Versucht zu entscheiden, ob eine Aussage wahr ist. |
| 5  | `constructor`             | Teilt ein UND im Goal auf.                         |
| 6  | `left`/`right`            | Beweist eine Seite eines ODER im Goal.             |
| 7ᵃ | `obtain ⟨h₁, h₂⟩ := h`    | Teilt ein UND in den Annahmen auf.                 |
| 7ᵇ | `obtain h := h \\| h`     | Teilt ein ODER in den Annahmen in zwei Fälle auf.  |

**Du** Woher weißt du das eigentlich alles?

**Robo** Keine Ahnung. War, glaube ich, vorinstalliert.
"
-/
Conclusion "Conclusion Logo L13:
Notations introdced so far:
`ℕ`, `0, 1, 2, …`, `=`, `≠` (shorthand for `¬(·=·)`), `Prop`, `True` (`(True : Prop)` is always true),
`False` (`(False : Prop)` is always false), `¬`, `∧`, `∨`, `(n : ℕ)`, `(A : Prop)`, `(ha : A)` (Proof that `(A : Prop)` is true),
 `(h : A ∧ B)` (Assumption with name `h`).
Tactics introduced so far:
`rfl` (proves `A = A`), `assumption`, `contradiction`, `decide`, `constructor`, `left`/`right`, `obtain ⟨h₁, h₂⟩ := h`, `obtain h := h \\| h`
"

DisabledTactic tauto
