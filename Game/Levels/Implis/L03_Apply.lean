import Game.Metadata

World "Implication"
Level 3

Title "Apply"

Introduction
"
Leider läuft das Telefonat nicht so gut. Er legt wieder auf und schüttelt mit dem Kopf.

**Operationsleiter**: Der Kollege auf der anderen Seite des Mondes versteht kein `revert`. Oder
er tut zumindest so. Habt Ihr noch eine andere Idee?

Er zieht eine Linie unter Euren Beweis, ergänzt ein durchgestrichenes ~`revert`~, und legt Euch
das Blatt ein zweites Mal vor.
"

Statement (A B : Prop) (h : A) (hAB : A → B) : B := by
  Hint "
    **Robo**: Vielleicht wäre es ohnehin eleganter gewesen, die gegebene Implikation anzuwenden.
    Probier doch mal `apply hAB at h`."
  Branch
    apply hAB
    Hint "
      **Robo**: Ich sagte `… at h`. Aber einfach nur `apply hAB` funktioniert offenbar auch.
      Jetzt hast Du sozusagen `hAB` auf das Beweisziel `B` angewendet, und musst nur
      noch `A` beweisen."
    assumption
  apply hAB at h
  Hint "**Du**: Ja, das kommt mir jetzt auch natürlich vor."
  assumption

Conclusion "Diesmal scheint das Telefonat erfolgreich zu verlaufen."

NewTactic apply
DisabledTactic revert tauto
