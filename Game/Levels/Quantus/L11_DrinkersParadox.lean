import Game.Metadata

World "Quantus"
Level 11

Title "Drinker's Paradox"

Introduction
"
**Du**: Könnt ihr eigentlich immer nur im Chor oder durcheinander reden?

Wieder herrscht längeres Schweigen. Dann auf einmal:

**Alle**: Es gibt unter uns eine Person, wenn die redet, dann reden alle!

Du kratzt Dich am Kopf.

**Robo**: Ist doch klar. Das ist auf jedem bewohnten Planeten so!

**Du**: Was??

**Robo**: Das ist eine Version vom Drinker's Paradox! Kennst du das nicht? Dann lies
das am besten Mal in deiner Handbibliothek nach! *In jeder Bar gibt es eine Person mit
der Eigenschaft, dass alle trinken, wenn sie trinkt.* Genauer gesagt: in jeder nicht-leeren Bar.

**Du**: Glaube ich nicht.

**Robo**: Glaube ich schon. Ich glaube sogar, du kannst das beweisen. Hier, probier mal!
"

open Function

Statement {People : Type} [h_nonempty : Nonempty People] (isDrinking : People → Prop) :
    ∃ (x : People), isDrinking x → ∀ (y : People), isDrinking y := by
  Hint "
    **Du**: Also, `{isDrinking}` ist wieder so ein Prädikat …
    Wenn `p` eine Person ist, ist `{isDrinking} p` eine Aussage,
    die wahr oder falsch ist. Soweit so gut.
    Und was bedeutet `Nonempty {People}`?

    **Robo**: Das ist Leansch für nicht-leer. Das heißt einfach, es gibt mindestens eine Person.
    Mit `use Classical.arbitrary {People}` kannst du dir eine `pers : {People}` aussuchen und verwenden,
    die es per Annahme gibt.

    **Du**: Und wie fang ich jetzt an?

    **Robo**: Ich sagte doch, schau am besten Mal in deine Handbibliothek.
    Wenn ich mich richtige erinnere, hilft eine Fallunterscheidung, ob die Aussage
    `∀ (y : {People}), {isDrinking} y` wahr oder falsch ist."
  Hint (hidden := true) "**Robo**: Schau mal `by_cases` an."
  by_cases h : ∀ y, isDrinking y
  · Hint (hidden := true) "
      **Du**: Und wen nehm ich jetzt?

      **Robo**: Wie gesagt, mit `use Classical.arbitrary {People}` kannst du eine beliebige
      Person auswählen und verwenden."
    use Classical.arbitrary People
    intro
    assumption
  · Hint (hidden := true) "**Robo**: Du könntest hier mit `push_neg at {h}` weitermachen."
    push_neg at h
    Hint (hidden := true) "**Du**: Also nach `{h}` existiert ja eine Person, die nicht trinkt. Könnte ich diese brauchen damit die Aussage trivialerweise wahr wird?

    **Robo**: Schau dir mal an wie man `obtain` auf die Annahme `{h}` anwenden könnte."
    choose p hp using h
    use p
    intro hp'
    Hint (hidden := true) "**Robo**: Was siehst du, wenn du `{hp}` und `{hp'}` anschaust?"
    contradiction

/-- TODO -/
TheoremDoc Classical.arbitrary as "Classical.arbitrary" in "Logic"

TheoremTab "Logic"
NewTheorem Classical.arbitrary
NewDefinition Nonempty

Conclusion
"
**Du**: Verstehe. Aber jetzt habe ich auch wirklich genug von dieser Prädikatenlogik!

**Robo**: Dann fliegen wir am besten weiter! Aber bevor du fragst – hier ist wieder ein Überblick, was du auf diesem Planeten gelernt hast.


|               | Beschreibung                |
|:--------------|:----------------------------|
| `∃`           | Existential-Quantifier      |
| `∀`           | Forall-Quantifier           |
| `Even n`      | `n` ist gerade              |
| `Odd n`       | `n` ist ungerade            |

|       | Taktik                    | Beispiel                                               |
|:------|:--------------------------|:-------------------------------------------------------|
| *13ᶜ* | `rw`                      | Umschreiben mit Gleichungen.                           |
| 15    | `ring`                    | Löst Gleichungen mit `+, -, *, ^`.                     |
| *4ᵇ*  | `decide`                  | Kann auch Aussagen zu konkreten Zahlen beantworten.    |
| 16    | `unfold`                  | Setzt visuell die Bedeutung einer Definition ein.      |
| 17    | `use`                     | Um ein `∃` im Goal anzugehen.                          |
| 18    | `choose x hx using h`     | Um ein `∃` in den Annahmen zu zerlegen.                |
| *8ᵇ*  | `intro`                   | Um ein `∀` im Goal anzugehen.                          |
| 19    | `push_neg`                | Für `¬∃` und `¬∀` im Goal.                             |
"
