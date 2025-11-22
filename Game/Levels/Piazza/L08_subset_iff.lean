import Game.Metadata

World "Piazza"
Level 8

Title ""

Introduction
"
**Sub**:  Du hast Recht.
Wir sollten die Besucher mal etwas mehr über Inklusionen ausfragen.
"

/-- `subset_iff` besagt, dass s₁ eine Teilmenge von s₂ genau dann ist, wenn alle Elemente in s₁ auch in s₂ enthalten sind. -/
TheoremDoc Set.subset_iff as "Set.subset_iff" in "Set"

namespace Set

Statement subset_iff {A : Type} {s₁ s₂ : Set A} : s₁ ⊆ s₂ ↔ ∀ {x : A}, x ∈ s₁ → x ∈ s₂ := by
  Hint "**Robo**: Das ist doch nur die Definition!

  **Robo** *(zu dir)*: Probier mal `tauto`.  Oder gleich `rfl`."
  Branch
    tauto
  rfl
end Set

NewDefinition Subset

/-- `subset_iff` besagt, dass s₁ eine Teilmenge von s₂ genau dann ist, wenn alle Elemente in s₁ auch in s₂ enthalten sind. -/
TheoremDoc Finset.subset_iff as "Finset.subset_iff" in "Set"
NewTheorem Finset.subset_iff


TheoremTab "Set"

Conclusion ""
