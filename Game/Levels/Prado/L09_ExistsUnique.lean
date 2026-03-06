import Game.Metadata
import Game.Levels.Prado.L08_exists_prime_and_dvd

World "Prado"
Level 9

Title ""

/-
Introduction"
**Robo**:  Aber so schwer ist das auch nicht.  Hier, schau dir diese Aufgabe mal an.
"
-/

Introduction "Intro Prado L09"

namespace Nat

Statement {a b : ℕ} (ha : 0 < a) (h : a ∣ b) : ∃! (m : ℕ), a * m = b := by
  /-
  Hint "
  **Du**: Ich sehe schon – `∃! m, P(m)` ist also die Notation für „es gibt genau ein `m`, für das `P(m)` gilt“.

  **Robo**: Genau.  Und das ist einfach definiert als „es existiert ein `m`,
  sodass (1) `P(m)` gilt und (2) jedes andere Element `m'`, für das `P(m')` gilt, bereits gleich `m` ist.
  Der erste Schritt ist also, ein geeignetes `m` zu finden, und dann `use _` zu verwenden."
  -/
  Hint "`∃! m, P(m)` is notation for 'there exists exactly one `m` for which `P(m)` holds'.
  It is defined as 'There exists a `m` , s.t., `P(m)` holds, and each other element `m'`, for which
  `P(m')` holds, is equal to `m`'. Try finding an appropriate `m` and apply `use _`"
  obtain ⟨w, hw⟩ := h
  use w
  -- Hint "**Robo**: Tatsächlich ergibt `use` auf `∃!` angewendet immer ein bisschen Chaos.
  -- Schick am besten immer gleich ein `simp` hinterher, dann wird es wieder lesbar."
  Hint "Applying `use` onto `∃!` is usually badly readable. Try `simp` directly afterwards"
  simp
  -- Hint "**Robo**: Jetzt hast du wie gesagt zwei Aussagen zu beweisen: (1) `{w}` erfüllt `a * {w} = b`,
  -- (2) `{w}` ist das einzige Element mit dieser Eigenschaft."
  Hint "Show two statements: (1) `{w}` satisfies `a * {w} = b` and (2) `{w}` is the only element with
  such a property"
  constructor
  · rw [hw]
  /-
  · Hint "
    **Robo**:  Super.  Jetzt also zur Eindeutigkeit.  Ich glaube, da könnte das Lemma
    `mul_eq_mul_left_iff` helfen:

    ```
    a * b = a * c ↔ b = c ∨ a = 0
    ```
    "
  -/
  · Hint "Try `mul_eq_mul_left_iff` which states
    ```
    a * b = a * c ↔ b = c ∨ a = 0
    ```
    "
    intro y hy
    rw [hw] at hy
    /-
    Branch
      rw [Nat.mul_left_cancel_iff] at hy -- TODO: _root_.mul_left_cancel_iff takes priority
      · assumption
      · assumption
    -/
    rw [mul_eq_mul_left_iff] at hy  -- `mul_eq_mul_left_iff` also used in ROBOTSWANA!
    obtain h | h := hy
    · assumption
    · linarith

NewDefinition ExistsUnique

/---/
TheoremDoc mul_eq_mul_left_iff as "mul_eq_mul_left_iff" in "+ *"
/---/
TheoremDoc mul_eq_mul_right_iff as "mul_eq_mul_right_iff" in "+ *"

TheoremTab "+ *"

NewTheorem mul_eq_mul_left_iff mul_eq_mul_right_iff

/-
/---/
TheoremDoc Nat.mul_left_cancel_iff as "mul_left_cancel_iff" in "ℕ"
/---/
TheoremDoc Nat.mul_right_cancel_iff as "mul_right_cancel_iff" in "ℕ"
NewTheorem Nat.mul_left_cancel_iff Nat.mul_right_cancel_iff
-/


TheoremTab "ℕ"
