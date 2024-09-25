import Game.MetaData

World "SetTheoryCore"
Level 6

Title "Teilmengen"

Introduction
"

-- eq_empty_iff_forall_not_mem

"

open Set

Statement Set.eq_empty_iff_forall_not_mem {A : Type _} (s : Set A) :
    s = ∅ ↔ ∀ x, x ∉ s := by
  rw [←subset_empty_iff]
  tauto
