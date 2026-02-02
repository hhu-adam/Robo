import Game.Metadata

World "Piazza"
Level 8

Title ""

/-
Introduction
"
**Sub**:  Du hast Recht.
Wir sollten die Besucher mal etwas mehr über Inklusionen ausfragen.
"
-/
Introduction "Intro Piazza L08"

/-- `subset_iff` says that s₁ is a subset of s₂ iff all elements in s₁ are also in s₂. -/
TheoremDoc Set.subset_iff as "Set.subset_iff" in "Set"

namespace Set

Statement subset_iff {A : Type} {s₁ s₂ : Set A} : s₁ ⊆ s₂ ↔ ∀ {x : A}, x ∈ s₁ → x ∈ s₂ := by
  /-
  Hint "**Robo**: Das ist doch nur die Definition!

  **Robo** *(zu dir)*: Probier mal `tauto`.  Oder gleich `rfl`."
  -/
  Hint "Try `tauto` or directly `rfl`"
  Branch
    tauto
  rfl
end Set

NewDefinition Subset

/-- `subset_iff` says that s₁ is a subset of s₂ iff all elements in s₁ are also in s₂. -/
TheoremDoc Finset.subset_iff as "Finset.subset_iff" in "Set"
NewTheorem Finset.subset_iff


TheoremTab "Set"

Conclusion ""
