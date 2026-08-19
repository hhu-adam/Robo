import Game.Levels.Fibre.L06_ExistsNonpos

World "Fibre"
Level 7

Introduction "Intro Fibre L07"

open Set FullGrind

Statement exists_mem_Ioo_val_nonneg {f : ℝ → ℝ} (hf1 : Continuous f)
    (hf2 : ∀ y, (f ⁻¹' {y}).ncard = 2) {x₁ x₂ : ℝ} (hx_lt : x₁ < x₂)
    (hx : f ⁻¹' {0} = {x₁, x₂}) : ∃ x ∈ Ioo x₁ x₂, 0 ≤ f x := by
  have hf2' : ∀ y, ((-f) ⁻¹' {y}).ncard = 2 := by
    intro y
    have h : (-f) ⁻¹' {y} = f ⁻¹' {-y} := by
      ext x
      simp [neg_eq_iff_eq_neg]
    rw [h]
    apply hf2
  have hx' : (-f) ⁻¹' {0} = {x₁, x₂} := by
    have h : (-f) ⁻¹' {0} = f ⁻¹' {0} := by
      ext x
      simp
    rw [h]
    apply hx
  obtain ⟨x, hx_mem, hx_le⟩ := by
    apply exists_mem_Ioo_val_nonpos _ hf2' hx_lt hx'
    exact continuous_neg_iff.mpr hf1
  use x
  constructor
  · assumption
  simp at hx_le
  grind

NewTheorem continuous_neg_iff neg_eq_iff_eq_neg
