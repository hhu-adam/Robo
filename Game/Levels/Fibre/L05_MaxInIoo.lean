import Game.Levels.Fibre.L04_ValueAtPair

World "Fibre"
Level 5

Introduction "Intro Fibre L05"

open Set FullGrind

/-- A function vanishing at both endpoints and positive in between attains its maximum over the closed interval strictly inside. -/
TheoremDoc max_mem_Ioo as "max_mem_Ioo" in "Fibre"

Statement max_mem_Ioo {f : ℝ → ℝ} {x₁ x₂ m : ℝ} (hx : x₁ < x₂) (h₁ : f x₁ = 0) (h₂ : f x₂ = 0)
    (hpos : ∀ x ∈ Ioo x₁ x₂, 0 < f x) (hm : m ∈ Icc x₁ x₂) (hmax : IsMaxOn f (Icc x₁ x₂) m) :
    m ∈ Ioo x₁ x₂ ∧ 0 < f m := by
  have hmid : (x₁ + x₂) / 2 ∈ Ioo x₁ x₂ := by
    grind
  have hmid_pos : 0 < f ((x₁ + x₂) / 2) := by
    grind
  have hle : f ((x₁ + x₂) / 2) ≤ f m := by
    apply hmax
    grind
  Branch
    grind
  constructor
  · grind
  · grind

TheoremTab "Fibre"
