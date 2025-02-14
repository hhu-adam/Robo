import Game.Metadata
import Game.Levels.Prado.L06_PrimeDvdPrime

namespace Nat

World "Prado"
Level 7

Title "Eindeutige Existenz"

Introduction"
**Robo**:  Aber so schwer ist des auch nicht.  Hier, schau dir diese Aufgabe mal an.
"

Statement {a b : ℕ} (ha : 0 < a) (h : a ∣ b) : ∃! (m : ℕ), a * m = b := by
  Hint "
  **Du**: Ich sehe schon – `∃! m, P(m)` ist also die Notation für „es gibt genau ein `m`, für das `P(m)` gilt“.

  **Robo**: Genau.  Und das ist einfach definiert als „es existiert ein `m`,
  sodass (1) `P(m)` gilt und (2) jedes andere Element `m'`, für das `P(m')` gilt, bereits gleich `m` ist.
  Der erste Schritt ist also, ein geeignetes `m` zu finden, und dann `use _` zu verwenden."
  obtain ⟨w, hw⟩ := h
  use w
  Hint "**Robo**: Tatsächlich ergibt `use` auf `∃!` angewendet immer ein bisschen Chaos.
  Schick am besten immer gleich ein `simp` hinterher, dann wird es wieder lesbar."
  simp
  Hint "**Robo**: Jetzt hast du wie gesagt zwei Aussagen zu beweisen: (1) `{w}` erfüllt `a * {w} = b`,
  (2) `{w}` ist das einzige Element mit dieser Eigenschaft."
  constructor
  · rw [hw]
  · Hint "
    **Robo**:  Super.  Jetzt also zur Eindeutigkeit.  Ich glaube, da könnte das Lemma
    `Nat.mul_left_cancel_iff` helfen.  Es besagt, dass für `0 < a` gilt:

    ```
    a * b = a * c ↔ b = c
    ```

    Es gibt genauso ein Lemma `mul_right_cancel_iff`, da ist alles entsprechend gedreht.
    "
    intro y hy
    rw [hw] at hy
    rw [Nat.mul_left_cancel_iff] at hy -- TODO: _root_.mul_left_cancel_iff takes priority
    · assumption
    · assumption



NewDefinition ExistsUnique
NewTheorem Nat.mul_left_cancel_iff Nat.mul_right_cancel_iff
TheoremTab "Nat"
