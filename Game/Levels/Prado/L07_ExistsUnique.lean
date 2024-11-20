import Game.Metadata
import Game.Levels.Prado.L06_PrimeDvdPrime

namespace Nat

World "Prado"
Level 7

Title "Eindeutige Existenz"

Introduction
"
`∃! m, a * m = b` sagt, \"es existiert ein eindeutiges `m`, so dass …\" und ist definiert als
`∃ m, [Aussage ist wahr für m] ∧ [m ist eindeutig]`.


Ich gebe dir noch zwei Hilfreiche Resultate mit. `Nat.mul_left_cancel_iff` sagt, dass für `0 < a`
folgendes  gilt.

```
a * b = a * c ↔ b = c
```

Das Resultat `Nat.mul_right_cancel_iff` ist entsprechend gedreht.
"

Statement {a b : ℕ} (ha : 0 < a) (h : a ∣ b) : ∃! (m : ℕ), a * m = b := by
  obtain ⟨w, hw⟩ := h
  use w
  Hint "**Robo**: `use` auf `∃!` angewendet gibt immer ein bisschen ein Chaos raus,
  am besten immer gleich ein `simp` hinterher, dann kann man besser arbeiten."
  simp
  Hint "Jetzt hast du zwei Teile, zuerst ein Beweis, dass die Aussage für dein gewähltes
  Element wahr ist, und rechts vom \"Und\" einen Beweis, dass es das einzige Element mit
  dieser Eigenschaft ist."
  constructor
  · rw [hw]
  · Hint "Dieser zweite Teil ist jetzt die Eindeutigkeit."
    intro y hy
    rw [hw] at hy
    rw [Nat.mul_left_cancel_iff] at hy -- TODO: _root_.mul_left_cancel_iff takes priority
    · assumption
    · assumption



NewDefinition ExistUnique
NewTheorem Nat.mul_left_cancel_iff Nat.mul_right_cancel_iff
TheoremTab "Nat"
