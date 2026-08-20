import Game.Levels.Bolzano.L01_MaxOnIcc

World "Bolzano"
Level 2

Introduction "Intro Bolzano L02"

open Set FullGrind

/-- Suppose `f` vanishes at the left endpoint and takes the value `f m` at the right one. Then
every value strictly between `0` and `f m` is attained strictly inside the interval. -/
TheoremDoc exists_mem_Ioo_eq_of_zero_left as "exists_mem_Ioo_eq_of_zero_left" in "Bolzano"

Statement exists_mem_Ioo_eq_of_zero_left {f : ℝ → ℝ} {a b m y : ℝ} (hf : Continuous f)
    (hab : a < b) (ha : f a = 0) (hb : f b = f m) (hy₀ : 0 < y) (hym : y < f m) :
    ∃ c ∈ Ioo a b, f c = y := by
  have hmem : y ∈ f '' Ioo a b := by
    apply intermediate_value_Ioo hab.le _
    · grind
    fun_prop
  obtain ⟨c, hc, hcy⟩ := hmem
  use c

TheoremTab "Bolzano"
