import Game.Metadata


World "Cantor"
Level 2

Title "Keine Fixpunkte"

Introduction
""

open Function Set

Statement not_isFixedPt_not : ¬ ∃ (A : Prop),  IsFixedPt (¬ .) A := by
  Hint "**Du**: Ja, `¬(·)` hat keinen Fixpunkt, keine Aussage kann gleichzeitig
    wahr und falsch sein!"
  Branch
    by_contra h
    rcases h with ⟨A, hA⟩
    unfold IsFixedPt at hA
    simp at hA -- a bit magical
  Branch
    push_neg
    intro P h
    unfold IsFixedPt at h
    Branch
      simp_all only [eq_iff_iff]
      simp only [not_iff_self] at h
    tauto
  unfold IsFixedPt
  tauto

theorem no_fixedpoints_of_not' : fixedPoints (¬ .) = ∅ :=
by
  apply eq_empty_iff_forall_not_mem.mpr
  intro P h
  simp only [mem_fixedPoints_iff] at h
  tauto

NewTheorem no_fixedpoints_of_not
TheoremTab "Function"
