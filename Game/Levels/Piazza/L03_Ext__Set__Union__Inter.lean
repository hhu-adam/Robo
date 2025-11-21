import Game.Metadata

World "Piazza"
Level 3

Title ""

-- Introduction
-- "
--   **Set**:  Wenn das zu einfach war – kennt ihr diese Aussage?
-- "
Introduction "`INTRO` Intro Piazza L03"

open Set

Statement (A B C : Set ℕ) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  /-
  Hint "
    **Du**:  `A B C : Set ℕ` heißt hier genau was?

    **Robo**:  Das heißt einfach, dass `A`, `B` und `C` *Teilmengen* von `ℕ` sind.

    **Du**:  `Set` bedeutet „subset“?

    **Robo**:  Wenn du so willst, ja.

    **Du**:  Dann *kenne* ich die Aussage wohl.
    Aber keine Ahnung, wie ich die hier beweisen könnte.

    **Ext**:  Kann ich dir sagen!  Da gibts ein Zauberwort, das heißt genau wie ich!!

    **Robo**:  Ach ja –
    `ext x` ersetzt eine Mengengleichheit `A = B` durch `x ∈ A ↔ x ∈ B`."
    -/
  Hint "`A B C : Set ℕ` means that `A`, `B` and `C` are subsets of `ℕ`. Therefore, `Set`
  can be interpreted as 'subset'. Use `ext x` to replace a set equation `A = B` with `x ∈ A ↔ x ∈ B`"
  ext x
  -- Hint "**Robo**:  Und jetzt wieder `simp`."
  Hint "Use `simp` again"
  simp -- simp only [mem_inter_iff, mem_union]
  /-
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
  -/
  Hint "Explain `simp`: `simp` looks for known equations and equivalences which would be currently
  applicable. `simp` uses all simplifications it can find. Currently the following simplifications
  were performed:
    ```
    {x} ∈ {A} ∩ {B} ↔ {x} ∈ {A} ∧ {x} ∈ {B}
    ```
    and
    ```
    {x} ∈ {B} ∪ {C} ↔ {x} ∈ {B} ∨ {x} ∈ {C}.
    ```
  "
  -- Hint (hidden := true)"
  --   **Robo**:  Den Rest schafft bestimmt `tauto`.
  -- "
  Hint (hidden := true) "The rest can be dealt with `tauto`"
  tauto

NewTactic ext
NewDefinition Set.union Set.inter
TheoremTab "Set"

Conclusion ""
