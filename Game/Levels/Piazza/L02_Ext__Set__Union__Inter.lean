import Game.Metadata

World "Piazza"
Level 2

Title ""

Introduction
"
  **Set**:  Wenn das zu einfach war – kennt ihr diese Aussage?
"

open Set

Statement (A B C : Set ℕ) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  Hint "
    **Du**:  `A B C : Set ℕ` heißt hier genau was?

    **Robo**:  Das heißt einfach, dass `A`, `B` und `C` *Teilmengen* von `ℕ` sind.

    **Du**:  `Set` bedeutet „subset“?

    **Robo**:  Wenn du so willst, ja.

    **Du**:  Ja, also jedenfalls *kenne* ich die Aussage dann wohl.
    Aber keine Ahnung, wie ich die wohl hier beweisen könnte.

    **Ext**:  Kann ich dir sagen!  Da gibts ein Zauberwort, das heißt genau wie ich!!

    **Robo**:  Ach ja –
    `ext x` ersetzt eine Mengengleichheit `A = B` durch `x ∈ A ↔ x ∈ B`."
  ext x
  Hint "**Robo**:  Und jetzt wieder `simp`."
  simp -- simp only [mem_inter_iff, mem_union]
  Hint "
    **Du**:  Was genau macht `simp` denn eigentlich?

    **Robo**:  `simp` sucht nach allgemein bekannten Gleichungen und Äquivalenzen,
    die gemeinhin als Vereinfachungen angesehen werden, und die gerade anwendbar wären.
    Alle Vereinfachungen, die `simp` findet, wendet es an.
    Gerade waren das beispielsweise Vereinfachungen der Form
    ```
    {x} ∈ {A} ∩ {B} ↔ {x} ∈ {A} ∧ {x} ∈ {B}
    ```
    und
    ```
    {x} ∈ {B} ∪ {C} ↔ {x} ∈ {B} ∨ {x} ∈ {C}.
    ```
  "
  Hint (hidden := true)"
    **Robo**:  Den Rest schafft bestimmt `tauto`.
  "
  tauto

NewTactic ext
NewDefinition Set.union Set.inter
TheoremTab "Set"

Conclusion ""
