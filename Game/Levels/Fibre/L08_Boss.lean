import Game.Levels.Fibre.L07_ExistsNonneg

World "Fibre"
Level 8

Introduction "Intro Fibre L08"

open Set FullGrind

Statement not_exists_continuous_ncard_preimage_eq_two :
    ¬ ∃ f : ℝ → ℝ, Continuous f ∧ ∀ y, (f ⁻¹' {y}).ncard = 2 := by
  intro ⟨f, hf₁, hf₂⟩
  obtain ⟨x₁, x₂, hx, hx_eq⟩ := ncard_eq_two_lt.mp (hf₂ 0)
  obtain ⟨fx₁_zero, fx₂_zero⟩ := val_eq_of_preimage_eq_pair hx_eq
  obtain ⟨c, ⟨hc₁, hc₂⟩, hc_nonpos⟩ := exists_mem_Ioo_val_nonpos hf₁ hf₂ hx hx_eq
  obtain fc_neg | fc_zero := hc_nonpos.lt_or_eq
  · obtain ⟨d, ⟨hd₁, hd₂⟩, hd_nonneg⟩ := exists_mem_Ioo_val_nonneg hf₁ hf₂ hx hx_eq
    obtain fd_zero | fd_pos := hd_nonneg.eq_or_lt
    · apply three_preimages hf₂ hd₁ hd₂ fx₁_zero fd_zero.symm fx₂_zero
    obtain ⟨e, he_mem, he_eq⟩ :=
      exists_mem_uIcc_eq hf₁ (mem_uIcc_of_le_of_le fc_neg.le fd_pos.le)
    rw [Set.mem_uIcc] at he_mem
    apply three_preimages hf₂ _ _ fx₁_zero he_eq fx₂_zero
    · grind
    · grind
  apply three_preimages hf₂ hc₁ hc₂ fx₁_zero fc_zero fx₂_zero
