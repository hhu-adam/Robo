import Game.MetaData

World "SetTheoryCore"
Level 5

Title "Teilmengen"

Introduction
"

"

-- For every type `X`, there are two important sets:
-- the empty set `∅ : Set X` and the universal set `univ : Set X` itself.
-- `∅` selects no elements of `X`, while `univ` selects every elements of `X`.

open Set


example (h : (univ : Set ℕ) ⊆ ∅) : (univ : Set ℕ) = ∅ := by
  Branch
    rw [←subset_empty_iff]
    assumption
  simp at h
  Branch
    rw [h]
  tauto
