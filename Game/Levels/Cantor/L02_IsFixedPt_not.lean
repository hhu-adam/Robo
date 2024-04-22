import Game.Metadata


World "Cantor"
Level 2

Title "Not fixed points"

Introduction
"
In this level you show that the set of the fixed points of the negation operator `¬ . : Prop → Prop` is empty.

"

open Function Set


-- Note: do we prefer `Not` instead of `(¬ .)`? -- JE: no
Statement no_fixedpoints_of_not : ¬ ∃ (x : Prop),  IsFixedPt (¬ .) x := by
  push_neg
  intro P h
  dsimp [IsFixedPt] at h
  Branch
    simp_all only [eq_iff_iff]
    simp only [not_iff_self] at h
  tauto



-- Statement no_fixedpoints_of_not' : fixedPoints (¬ .) = ∅ :=
-- by
--   apply eq_empty_iff_forall_not_mem.mpr
--   intro P h
--   simp only [mem_fixedPoints_iff] at h
--   tauto






#check IsEmpty
