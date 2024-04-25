import Game.Metadata


World "Cantor"
Level 2

Title "Not fixed points"

Introduction
"
In this level you show that the set of the fixed points of the negation operator `¬ . : Prop → Prop` is empty.

Die Funktion `¬ : Prop → Prop` hat keine Fixpunkte.


"

open Function Set

Statement no_fixedpoints_of_not : ¬ ∃ (A : Prop),  IsFixedPt (¬ .) A := by
  push_neg
  intro P h
  unfold IsFixedPt at h
  Branch
    simp_all only [eq_iff_iff]
    simp only [not_iff_self] at h
  tauto

-- theorem no_fixedpoints_of_not' : fixedPoints (¬ .) = ∅ :=
-- by
--   apply eq_empty_iff_forall_not_mem.mpr
--   intro P h
--   simp only [mem_fixedPoints_iff] at h
--   tauto

NewTheorem no_fixedpoints_of_not
TheoremTab "Function"
