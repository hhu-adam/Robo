import Game.Levels.Bolzano.L03_IntermediateValue

World "Bolzano"
Level 4

Introduction "Intro Bolzano L04"

open Set FullGrind

/-- If neither endpoint takes the value `y`, then `y` is already attained strictly inside the interval. -/
TheoremDoc exists_mem_Ioo_eq as "exists_mem_Ioo_eq" in "Bolzano"

Statement exists_mem_Ioo_eq {f : ℝ → ℝ} {a b y : ℝ} (hf : Continuous f) (hab : a < b)
    (hy : y ∈ uIcc (f a) (f b)) (ha : f a ≠ y) (hb : f b ≠ y) :
    ∃ c ∈ Ioo a b, f c = y := by
  have h : ∃ c ∈ uIcc a b, f c = y := exists_mem_uIcc_eq hf hy
  obtain ⟨c, hc, hcy⟩ := h
  rw [Set.uIcc_of_le hab.le, Set.mem_Icc] at hc
  refine ⟨c, ⟨?_, ?_⟩, hcy⟩ <;> grind

NewTheorem Set.uIcc_of_le Set.mem_Icc

TheoremTab "Bolzano"
