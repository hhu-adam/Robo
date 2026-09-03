import Game.Levels.Bolzano.L02_CrossLeft

World "Bolzano"
Level 3

Introduction "Intro Bolzano L03"

open Set FullGrind

/-- The mirror image of the previous level: this time the zero sits at the right endpoint and
the value `f m` at the left one. -/
TheoremDoc exists_mem_Ioo_eq_of_zero_right as "exists_mem_Ioo_eq_of_zero_right" in "Bolzano"

Statement exists_mem_Ioo_eq_of_zero_right {f : ℝ → ℝ} {a b m y : ℝ} (hf : Continuous f)
    (hab : a < b) (ha : f a = f m) (hb : f b = 0) (hy₀ : 0 < y) (hym : y < f m) :
    ∃ c ∈ Ioo a b, f c = y := by
  have hmem : y ∈ f '' Ioo a b := by
    apply intermediate_value_Ioo' hab.le _
    · grind
    fun_prop
  obtain ⟨c, hc, hcy⟩ := hmem
  use c

TheoremTab "Bolzano"
