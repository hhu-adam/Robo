import Game.Levels.Bolzano.L02_MemUIcc

World "Bolzano"
Level 3

Introduction "Intro Bolzano L03"

open Set FullGrind

/-- Intermediate value theorem: a continuous function takes every value between `f a` and `f b`. -/
TheoremDoc exists_mem_uIcc_eq as "exists_mem_uIcc_eq" in "Bolzano"

Statement exists_mem_uIcc_eq {f : ℝ → ℝ} {a b y : ℝ} (hf : Continuous f)
    (hy : y ∈ uIcc (f a) (f b)) : ∃ c ∈ uIcc a b, f c = y := by
  have h : y ∈ f '' uIcc a b := intermediate_value_uIcc (f := f) hf.continuousOn hy
  obtain ⟨c, hc, hcy⟩ := h
  use c

NewTheorem intermediate_value_uIcc Continuous.continuousOn

TheoremTab "Bolzano"
