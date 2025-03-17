import Game.Metadata

World "Piazza"
Level 3

Title "" -- "Teilmengen"

Introduction
"
**Sub**:  Du hast Recht.
Wir sollten die Besucher mal etwas mehr über Inklusionen ausfragen.
"

/---/
TheoremDoc Set.subset_iff as "subset_iff" in "Set"

namespace Set

Statement subset_iff {A : Type} {s₁ s₂ : Set A} : s₁ ⊆ s₂ ↔ ∀ {x : A}, x ∈ s₁ → x ∈ s₂ := by
  Hint "**Robo**: Das ist doch nur die Definition!

  **Robo** *(zu dir)*: Probier mal `tauto`.  Oder gleich `rfl`."
  Branch
    tauto
  rfl


NewDefinition Subset

TheoremTab "Set"

Conclusion ""
