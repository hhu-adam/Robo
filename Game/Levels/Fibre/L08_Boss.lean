import Game.Levels.Fibre.L07_ExistsNonneg

World "Fibre"
Level 8

Introduction "Intro Fibre L08"

open Set FullGrind

/-- No continuous function on the real line takes every value exactly twice. -/
TheoremDoc not_exists_continuous_ncard_preimage_eq_two as "not_exists_continuous_ncard_preimage_eq_two" in "Fibre"

Statement not_exists_continuous_ncard_preimage_eq_two :
    ¬ ∃ f : ℝ → ℝ, Continuous f ∧ ∀ y, (f ⁻¹' {y}).ncard = 2 := by
  intro h
  obtain ⟨f, hf₁, hf₂⟩ := h
  have h_pair : ∃ x y, x < y ∧ f ⁻¹' {0} = {x, y} := ncard_eq_two_lt.mp (hf₂ 0)
  obtain ⟨x₁, x₂, hx, hx_eq⟩ := h_pair
  have h_ends : f x₁ = 0 ∧ f x₂ = 0 := val_eq_of_preimage_eq_pair hx_eq
  obtain ⟨fx₁_zero, fx₂_zero⟩ := h_ends
  have h_c : ∃ x ∈ Ioo x₁ x₂, f x ≤ 0 := exists_mem_Ioo_val_nonpos hf₁ hf₂ hx hx_eq
  obtain ⟨c, ⟨hc₁, hc₂⟩, hc_nonpos⟩ := h_c
  have hc_cases : f c < 0 ∨ f c = 0 := by
    grind
  obtain fc_neg | fc_zero := hc_cases
  · have h_d : ∃ x ∈ Ioo x₁ x₂, 0 ≤ f x := exists_mem_Ioo_val_nonneg hf₁ hf₂ hx hx_eq
    obtain ⟨d, ⟨hd₁, hd₂⟩, hd_nonneg⟩ := h_d
    have hd_cases : 0 = f d ∨ 0 < f d := by
      grind
    obtain fd_zero | fd_pos := hd_cases
    · apply three_preimages hf₂ hd₁ hd₂ fx₁_zero fd_zero.symm fx₂_zero
    have h_e : ∃ e ∈ Ioo x₁ x₂, f e = 0 :=
      exists_zero_of_neg_of_pos hf₁ ⟨hc₁, hc₂⟩ ⟨hd₁, hd₂⟩ fc_neg fd_pos
    obtain ⟨e, ⟨he₁, he₂⟩, he_eq⟩ := h_e
    apply three_preimages hf₂ he₁ he₂ fx₁_zero he_eq fx₂_zero
  apply three_preimages hf₂ hc₁ hc₂ fx₁_zero fc_zero fx₂_zero

TheoremTab "Fibre"
