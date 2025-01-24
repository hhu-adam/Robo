
import Game.MetaData

World "SetTheoryCore"
Level 7

Title "Teilmengen"

Introduction
"

-- mem_union
-- mem_inter_iff
-- mem_setOf
-- mem_compl

"

open Set

Statement (A B C : Set ℕ) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  Branch
    rw [mem_inter_iff, mem_union, mem_union, mem_inter_iff, mem_inter_iff]
    tauto
  simp
  tauto
  --

-- we need to make this part of the set planet.
#check mem_setOf
#check mem_compl

example
    (A B C : Set ℕ) : (A \ B)ᶜ ∩ (C \ B)ᶜ = ((univ \ A) \ C) ∪ (univ \ Bᶜ) := by
  ext x
  simp only [mem_inter_iff, mem_union, mem_diff, mem_compl_iff, mem_compl_iff]
  tauto
