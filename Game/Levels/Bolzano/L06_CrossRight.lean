import Game.Levels.Bolzano.L05_CrossLeft

World "Bolzano"
Level 6

Introduction "Intro Bolzano L06"

open Set FullGrind

Statement exists_mem_Ioo_eq_of_zero_right {f : ℝ → ℝ} {a b m y : ℝ} (hf : Continuous f)
    (hab : a < b) (ha : f a = f m) (hb : f b = 0) (hy₀ : 0 < y) (hym : y < f m) :
    ∃ c ∈ Ioo a b, f c = y := by
  refine exists_mem_Ioo_eq hf hab ?_ ?_ ?_
  · rw [Set.uIcc_comm]
    apply mem_uIcc_of_le_of_le <;> grind
  · grind
  · grind

NewTheorem Set.uIcc_comm
