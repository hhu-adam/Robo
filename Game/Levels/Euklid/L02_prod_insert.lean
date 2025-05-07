import Game.Metadata

World "Euklid"
Level 2
Title ""

Introduction "Ein Stückchen weiter den Gang entlang seht ihr wieder ein aufgeschlagenes Buch auf der Erde."

open Finset
namespace Nat

Statement (p : ℕ) (hp : Prime p) (A : Finset ℕ): (∃ a ∈ A, p ∣ a) → p ∣ ∏ a ∈ A, a := by
  Hint "**Robo**: Diese Zeile sieht auch sehr vernünftig aus:
  wenn ein Primfaktor einen Faktor `a` eines Produkts teilt, dann teilt er sicher auch das ganze Produkt.

  **Du**:  Bereits die erste „Beweiszeile“ ist aber nicht einmal im Ansatz lebsbar.

  **Robo**:  Nein, ist sie nicht. Aber probieren wirs wieder selbst.
  Wir fangen natürlich mit `intro` an.
  "
  intro h
  Hint "**Robo**:  Und jetzt zerlegen wir die Annahme `{h}` in ihre drei Bestandteile."
  obtain ⟨a, ha, hpa⟩ := h
  Hint "
    **Du**:  Vermutlich will ich jetzt den Faktor `{a}` irgendwie aus dem Produkt heraustrennen?

    **Robo**:  Ja, das müsste helfen.  Ich denke, du wirst so etwas brauchen wie `insert_erase`.
  "
  Hint (hidden := true) "
    **Robo**:  Probier mal `rw [insert_erase {ha}]`.
  "
  rw [← insert_erase ha]
  Hint "
    **Robo**:  Und jetzt verwendest du `prod_insert`, und den Faktor tatsächlich herauszuziehen.
  "
  rw [prod_insert]
  Hint (hidden := true) "
    **Robo**:  Der Rest sollte jetzt einfach sein.  Wir hatten ja schon `Prime.dvd_mul` bewiesen.
  "
  · rw [Prime.dvd_mul]
    · left
      assumption
    · assumption
  · simp

/---/
TheoremDoc Finset.prod_insert as "prod_insert" in "∑ Π"

NewTheorem Finset.prod_insert
