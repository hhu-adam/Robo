import Game.Metadata

import Game.Levels.Sum.L06_SumComm

World "Sum"
Level 7
Title "Zusammenfassung"

Introduction
"
**Du**: Robo, gib mir doch nochmals eine Übersicht, bitte.

**Robo**: Aber klar:

|                      | Beschreibung                              |
|:---------------------|:------------------------------------------|
| `Fin n`              | Ist ein Typ mit Zahlen $0, \\ldots, n-1$. |
| `∑ (i : Fin n), a i` | $\\sum_{i=0}^{n-1} a_i$                   |
| `↑i`                 | Eine Coersion, z.B. `Fin n → ℕ`.          |

und

|    | Taktik                    | Beispiel                             |
|:---|:--------------------------|:-------------------------------------|
| 21 | `simp`                    | Simplifikation.                      |
| 22 | `induction n`             | Induktion über $n$                   |

Da kommt hinter einem Turm plötzlich ein besonders großer Babylonier hervor, schaut euch
bedrohlich an und fragt in tiefer Stimme:
"

open Fin

open BigOperators

Statement (m : ℕ) : (∑ i : Fin (m + 1), i ^ 3) = (∑ i : Fin (m + 1), i) ^ 2 := by
  Hint "**Du**: Gulp. Naja das wird schon klappen. Also man fängt wieder mit Induktion an …"
  induction m with n n_ih
  Hint "**Du**: Also den Induktionsanfang kann man einfach zeigen …"
  simp
  Hint (hidden := true) "**Robo**: Und jetzt wieder `rw [sum_univ_castSucc]` und `simp`, um vorwärts zu
  kommen!"
  rw [Fin.sum_univ_castSucc]
  simp
  Hint "**Robo**: Siehst du die Induktionshypothese hier drin?"
  rw [n_ih]
  Hint "**Du**: Okay, damit habe ich die linke Seite der Gleichung ziemlich gut bearbeitet.
  Aber, ehm, mit der Rechten komme ich nicht weiter …

  Der Babylonier schaut dich finster an.

  **Du**: Ich will `sum_univ_castSucc` auf der rechten Seite anwenden, aber es gibt mehrere Orte, wo das Lemma passen würde, und ich will es nur an einer bestimmten Stelle anwenden.

  **Robo**:
  Mit `rw [sum_univ_castSucc (n := {n} + 1)]` kannst du angeben, wo genau.

  **Du**: Was bedeutet das?

  **Robo** Das Lemma hat eine Annahme `n` und du sagst ihm explizit, was es für dieses `n`
  einsetzen muss, nämlich `{n} + 1`"
  Branch
    rw [Fin.sum_univ_castSucc]
    Hint "**Robo**: Das hat jetzt einfach `Fin.sum_univ_castSucc` am ersten Ort angewendet,
    wo das möglich war. Das ist nicht so ideal, die linke Seite war schon okay.

    **Robo**: Geh doch zurück und bring `rw` dazu am anderen Ort umzuschreiben."
  rw [Fin.sum_univ_castSucc (n := n + 1)]
  simp
  Hint "**Robo**: `add_pow_two` ist auch noch nützlich!"
  rw [add_pow_two]
  Hint "**Du**: Ich glaube, ich sehe hier eine Gaußsche Summe!!

  **Robo**: Ich habe dir das vorhin temporär als `arithmetic_sum` gespeichert.
  Das kannst du jetzt benutzen."
  rw [arithmetic_sum]
  Hint "**Du**: Jetzt sollten es eigentlich nur noch arithmetische Operationen sein."
  ring

NewTheorem add_pow_two
TheoremTab "Sum"

Conclusion "Der Babylonier denkt ganz lange nach, und ihr bekommt das Gefühl, dass er gar nie
aggressiv war, sondern nur eine sehr tiefe Stimme hat.

Mit einem kleinen Erdbeben setzt er sich hin und winkt euch dankend zu."
