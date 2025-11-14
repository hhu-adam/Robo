import Game.Metadata

World "Euklid"
Level 2
Title ""

/- Introduction "Ein Stückchen weiter den Gang entlang seht ihr wieder ein aufgeschlagenes Buch auf der Erde." -/
Introduction "`INTRO` Intro Euklid L02"

open Finset
namespace Nat

Statement (b : ℕ) (A : Finset ℕ): (∃ a ∈ A, b ∣ a) → b ∣ ∏ a ∈ A, a := by
  /-
  Hint "**Robo**: Diese Zeile sieht auch sehr vernünftig aus:
  wenn eine Zahl `{b}` einen Faktor `a` eines Produkts teilt, dann teilt sie sicher auch das ganze Produkt.

  **Du**:  Bereits die erste „Beweiszeile“ ist aber nicht einmal im Ansatz lebsbar.

  **Robo**:  Nein, ist sie nicht. Aber probieren wirs wieder selbst.
  Wir fangen natürlich mit `intro` an.
  "
  -/
  Hint "Goal: if `{b}` divides factor `a` of a product then it also divides the product.
  Try `intro`"
  intro h
  /- Hint "**Robo**:  Und jetzt zerlegen wir die Annahme `{h}` in ihre drei Bestandteile." -/
  Hint "Disect `{h}` into its constituents"
  obtain ⟨a, ha, hpa⟩ := h
  /-
  Hint "
    **Du**:  Vermutlich will ich jetzt den Faktor `{a}` irgendwie aus dem Produkt heraustrennen?

    **Robo**:  Ja, das müsste helfen.  Ich denke, du wirst so etwas brauchen wie `insert_erase`.
  "
  -/
  Hint "Seperate factor `{a}` out of product by using `insert_erase`"
  /-
  Hint (hidden := true) "
    **Robo**:  Probier mal `rw [← insert_erase {ha}]`.
  "
  -/
  Hint (hidden := true) "Try rewriting with `rw [← insert_erase {ha}]`"
  rw [← insert_erase ha]
  /-
  Hint "
    **Robo**:  Und jetzt verwendest du `prod_insert`, und den Faktor tatsächlich herauszuziehen.
  "
  -/
  Hint "Use `prod_insert` to actually extract the factot"
  rw [prod_insert]
  /-
  Hint (hidden := true) "
    **Robo**:  Der Rest sollte jetzt einfach sein.
  "
  -/
  Hint (hidden := true) "The rest should be easy"
  · obtain ⟨k, hk⟩ := hpa
    use k * ∏ x ∈ erase A a, x
    rw [hk]
    ring
  simp

/---/
TheoremDoc Finset.prod_insert as "prod_insert" in "∑ Π"

NewTheorem Finset.prod_insert
