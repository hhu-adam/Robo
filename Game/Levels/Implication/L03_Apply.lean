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
    **Robo**:  Vielleicht wäre es ohnehin eleganter gewesen, die gegebene Implikation anzuwenden.
    Probier doch mal `apply hAB at h`."
  Branch
    apply hAB
    Hint "
      **Robo**:  Ich sagte `… at h`. Aber einfach nur `apply hAB` funktioniert offenbar auch.
      Jetzt hast Du sozusagen `hAB` auf das Beweisziel `B` angewendet, und musst nur
      noch `A` beweisen."
    assumption
  apply hAB at h
  Hint "**Du**: Ja, das kommt mir jetzt auch natürlich vor."
  assumption

Conclusion "Diesmal scheint das Telefonat erfolgreich zu verlaufen."

/--
Sind eine Annahme `h : A` und eine Implikation `hAB : A → B` gegeben, so
verwandelt `apply hAB at h` die gegebene Annahme in die Annahme `h : B`.
Ist `B` unser Beweisziel, können wir mit `apply hAB` auch rückwärts argumentieren und
erhalten `A` als neues Beweisziel.   In beiden Fällen kann die Implikation `hAB` wahlweise
als Annahme gegeben oder ein bereits bekanntes Lemma sein.


## Beispiel

Gegeben sei für `n : ℕ` folgendes Lemma:
```
lemma lem (h : n ≤ 0) : n = 0
```

Finden wir nun als Beweisziel

```
Goal
  n = 0
```

vor, so ändert `apply lem` das Beweisziel zu `n ≤ 0`.

Anders herum, falls wir eine Annahme `g : m ≤ 0` in unseren Annahmen finden, können wir
diese mit `apply lem at g` zu `g : m = 0` umwandeln.

(Das Lemma ist gemeinhin als `Nat.eq_zero_of_le_zero` bekannt.)
-/
TacticDoc apply

NewTactic apply
DisabledTactic revert tauto
