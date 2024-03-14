import Game.Metadata

World "Implication"
Level 1

Title "Intro"

Introduction
"
**Operationsleiter**: Hier, zum Beispiel:
"

Statement (A B : Prop) (hB : B) : A → (A ∧ B) := by
  Hint "
    **Operationsleiter**:  Die Arbeiten meinen, das wäre so richtig und wir würden das dringend
    brauchen. Aber keiner kann es mir beweisen.

    **Du**: Einen Moment. Das ist ja gerade so eine Implikation (`\\to`). Wir nehmen an,
    dass `{B}` gilt, und wollen zeigen, dass dann gilt `{A}` impliziert `{A} und {B}`. Ja,
    klar! Natürlich stimmt das.

    Der Operationsleiter sieht dich erwartungsvoll an.

    **Du** *(leise zu Robo)*:  Soll ich ihm `tauto` aufschreiben?

    **Robo** *(leise zurück)*:  So wie der aussieht, fürchte ich, das wird er auch nicht verstehen.
      Schreib den Beweis lieber aus.

    **Du**: Aber wie denn?  Ich glaube, ich würde als erstes gern so etwas sagen wie 'Nehmen wir
    also an, `{A}` gilt …'

    **Robo**: Ja, gute Idee. Wähle dazu für deine Annahme einfach einen Namen, zum Beispiel `h`,
    und schreib `intro h`."
  intro hA
  Hint "
    **Du**: Okay. Jetzt habe ich also sowohl `{A}` als auch `{B}` in meinen Annahmen und
    muss `{A} ∧ {B}` zeigen.

    **Robo**:  Genau. Und wie das geht, weißt du ja schon."
  constructor
  assumption
  assumption

Conclusion
"
**Operationsleiter**: Perfekt!  Danke schön!

Er geht zu einer Schalttafel und ein paar Knöpfe. Irgendwo setzt sich lautstark ein
Förderband in Bewegung.

**Operationsleiter**: Habt Ihr vielleicht noch ein paar Minuten?
"

/--
`intro x` wird für Goals der Form `A → B` oder `∀ x, P x` verwendet.
Dadurch wird die Implikationsprämisse (oder das Objekt `x`) den Annahmen hinzugefügt.

## Hilfreiche Resultate

* `revert h` macht das Gegenteil von `intro`.
-/
TacticDoc intro

NewTactic intro
DisabledTactic tauto
