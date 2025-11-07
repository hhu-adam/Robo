import Game.Metadata

World "Implis"
Level 3

Title "" -- "Apply"

/-
Introduction
"
Leider läuft das Telefonat nicht so gut. Er legt wieder auf und schüttelt mit dem Kopf.

**Operationsleiter**: Der Kollege auf der anderen Seite des Mondes versteht kein `revert`. Oder
er tut zumindest so. Habt Ihr noch eine andere Idee?

Er zieht eine Linie unter Euren Beweis, ergänzt ein durchgestrichenes ~`revert`~, und legt Euch
das Blatt ein zweites Mal vor.
"
-/
Introduction "Intro Implis L03: This Level does not know `revert`. Try proof without `revert`"

Statement (A B : Prop) (h : A) (hAB : A → B) : B := by
  /-
  Hint "
    **Robo**: Vielleicht wäre es ohnehin eleganter gewesen, die gegebene Implikation anzuwenden.
    Probier doch mal `apply hAB at h`."
  -/
  Hint "Us the given implication by trying `apply hAB at h`"
  Branch
    apply hAB
    /-
    Hint "
      **Robo**: Ich sagte `… at h`. Aber einfach nur `apply hAB` funktioniert offenbar auch.
      Jetzt hast Du sozusagen `hAB` auf das Beweisziel `B` angewendet, und musst nur
      noch `A` beweisen."
    -/
    Hint "`… at h` was tried but simply `apply hAB` works as well. `hAB` was applied to goal `B` and now
    `A` has to be proven."
    assumption
  apply hAB at h
  -- Hint "**Du**: Ja, das kommt mir jetzt auch natürlich vor."
  Hint "This should seem obvious now"
  assumption

-- Conclusion "Diesmal scheint das Telefonat erfolgreich zu verlaufen."
Conclusion "`CONC` Conclusion Implis L03"

NewTactic apply
DisabledTactic revert tauto
