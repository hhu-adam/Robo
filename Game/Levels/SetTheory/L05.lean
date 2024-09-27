import Game.Metadata

World "SetTheory"
Level 5

Title "Antisymmetrie"

Introduction
"
Am Anfang hatten wir gesehen, dass man Mengengleichheit durch
`ext x` angehen kann.

Hier lernen wir eine nützliche Alternative:

`rw [Set.Subset.antisymm_iff]`

mit dem Theorem

```
Set.Subset.antisymm_iff : A = B ↔ A ⊆ B ∧ B ⊆ A
```

welches wir hier beweisen.
"

open Set

Statement Set.Subset.antisymm_iff {α : Type} {A B : Set α} : A = B ↔ A ⊆ B ∧ B ⊆ A := by
  constructor
  · intro h
    Hint (hidden := true) "Ersetz mal `{A}` durch `{B}`."
    rw [h]
    tauto
  · intro h
    Hint (hidden := true) "Diesen Teil würde ich trotzdem mit unserem Schema zeigen,
    also `ext x` zuerst…"
    ext i
    tauto

TheoremTab "Set"

Conclusion ""
-- TODO: Maybe exercise using this Lemma? Although `ext x` seems always the superior approach.
