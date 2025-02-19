import Game.Metadata
import Game.Levels.SetTheory.L10_Morgan

World "SetTheory"
Level 11

Title "" -- "Strikte Teilmenge"

Introduction
"
Die Dame geht mit ihrem Einkauf davon.

**Verkäufer**: Wisst ihr, seit einer Weile redet sie eigentlich immer über den Unterschied
von `⊂` und `⊆`, aber heute nicht. Könnt ihr mir schon mal helfen, damit ich morgen
gewappnet bin?
"

open Set

/--  -/
Statement (A B : Set ℕ) (h : A ⊂ B) : ∃ x, x ∈ B \ A := by
  obtain ⟨h₁, h₂⟩ := h
  rw [subset_def] at h₂
  rw [not_forall] at h₂
  obtain ⟨x, hx⟩ := h₂
  use x
  rw [not_imp] at hx
  rw [mem_diff]
  assumption

NewTheorem Set.subset_def Set.ssubset_def not_imp Set.mem_diff
TheoremTab "Set"
