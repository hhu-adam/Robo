import Game.Levels.Fibre.L04_ValueAtPair

World "Fibre"
Level 5

Introduction "Intro Fibre L05"

open Set FullGrind

Statement max_mem_Ioo {f : ℝ → ℝ} {x₁ x₂ m : ℝ} (hx : x₁ < x₂) (h₁ : f x₁ = 0) (h₂ : f x₂ = 0)
    (hpos : ∀ x ∈ Ioo x₁ x₂, 0 < f x) (hm : m ∈ Icc x₁ x₂) (hmax : IsMaxOn f (Icc x₁ x₂) m) :
    m ∈ Ioo x₁ x₂ ∧ 0 < f m := by
  rw [isMaxOn_iff] at hmax
  have hmid : (x₁ + x₂) / 2 ∈ Ioo x₁ x₂ := by
    constructor <;> grind
  have hmid_pos : 0 < f ((x₁ + x₂) / 2) := hpos _ hmid
  have hle := hmax _ (Ioo_subset_Icc_self hmid)
  have hm_pos : 0 < f m := by grind
  obtain ⟨hl, hr⟩ := hm
  exact ⟨⟨by grind, by grind⟩, hm_pos⟩

NewTheorem isMaxOn_iff Set.Ioo_subset_Icc_self
