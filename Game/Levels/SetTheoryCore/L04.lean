import Game.MetaData

World "SetTheoryCore"
Level 4

Title "Teilmengen"

Introduction
"

"

-- For every type `X`, there are two important sets:
-- the empty set `∅ : Set X` and the universal set `univ : Set X` itself.
-- `∅` selects no elements of `X`, while `univ` selects every elements of `X`.

open Set

--#check Set.subset_def
--#check Subset.trans

Statement : (∅ : Set X) ⊆ univ := by
  tauto
