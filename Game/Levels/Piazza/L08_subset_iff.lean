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
Introduction "`INTRO` Intro Piazza L08"

/---/
TheoremDoc Set.subset_iff as "subset_iff" in "Set"

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

/---/
TheoremDoc Finset.subset_iff as "subset_iff" in "Set"
NewTheorem Finset.subset_iff


TheoremTab "Set"

-- Conclusion ""
Conclusion "Conclusion Piazza L08"
