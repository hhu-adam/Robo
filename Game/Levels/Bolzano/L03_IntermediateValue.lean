import Game.Levels.Bolzano.L02_MemUIcc

World "Bolzano"
Level 3

Introduction "Intro Bolzano L03"

open Set FullGrind

Statement exists_mem_uIcc_eq {f : ℝ → ℝ} {a b y : ℝ} (hf : Continuous f)
    (hy : y ∈ uIcc (f a) (f b)) : ∃ c ∈ uIcc a b, f c = y := by
  obtain ⟨c, hc, hcy⟩ := intermediate_value_uIcc (f := f) hf.continuousOn hy
  use c

NewTheorem intermediate_value_uIcc Continuous.continuousOn
