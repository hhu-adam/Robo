import Game.Levels.Fibre.L05_MaxInIoo

World "Fibre"
Level 6

Introduction "Intro Fibre L06"

open Set FullGrind

Statement exists_mem_Ioo_val_nonpos {f : ℝ → ℝ} (hf1 : Continuous f)
    (hf2 : ∀ y, (f ⁻¹' {y}).ncard = 2) {x₁ x₂ : ℝ} (hx_lt : x₁ < x₂)
    (hx : f ⁻¹' {0} = {x₁, x₂}) : ∃ x ∈ Ioo x₁ x₂, f x ≤ 0 := by
  by_contra! hc
  obtain ⟨fx₁_zero, fx₂_zero⟩ := val_eq_of_preimage_eq_pair hx
  obtain ⟨m, hm_mem, hm_max⟩ := exists_isMaxOn_Icc hf1 hx_lt.le
  obtain ⟨hm_Ioo, hm_pos⟩ := max_mem_Ioo hx_lt fx₁_zero fx₂_zero hc hm_mem hm_max
  obtain ⟨hm₁, hm₂⟩ := hm_Ioo
  rw [isMaxOn_iff] at hm_max
  have hself : m ∈ f ⁻¹' {f m} := rfl
  obtain ⟨x₃, x₃_mem, x₃_neq⟩ := exists_second_mem (hf2 _) hself
  let y₀ := f m / 2
  have y₀_pos : 0 < y₀ := by grind
  have y₀_lt : y₀ < f m := by grind
  obtain ⟨a, ⟨ha₁, ha₂⟩, hfa⟩ :=
    exists_mem_Ioo_eq_of_zero_left hf1 hm₁ fx₁_zero rfl y₀_pos y₀_lt
  obtain ⟨b, ⟨hb₁, hb₂⟩, hfb⟩ :=
    exists_mem_Ioo_eq_of_zero_right hf1 hm₂ rfl fx₂_zero y₀_pos y₀_lt
  /- case 1: `x₃` lies left of `x₁` -/
  obtain h_lt | h_ge := lt_or_ge x₃ x₁
  · obtain ⟨c, ⟨hc₁, hc₂⟩, hfc⟩ :=
      exists_mem_Ioo_eq_of_zero_right hf1 h_lt x₃_mem fx₁_zero y₀_pos y₀_lt
    exact three_preimages hf2 (by grind) (by grind) hfc hfa hfb
  /- case 2: `x₃` lies right of `x₂` -/
  obtain h_gt | h_le := lt_or_ge x₂ x₃
  · obtain ⟨c, ⟨hc₁, hc₂⟩, hfc⟩ :=
      exists_mem_Ioo_eq_of_zero_left hf1 h_gt fx₂_zero x₃_mem y₀_pos y₀_lt
    exact three_preimages hf2 (by grind) (by grind) hfa hfb hfc
  /- case 3: `x₃` lies inside `Ioo x₁ x₂` -/
  have x₃_mem_Ioo : x₃ ∈ Ioo x₁ x₂ := by grind
  let t₀ := (x₃ + m) / 2
  have t₀_mem : t₀ ∈ Ioo x₁ x₂ := by grind
  obtain h_eq | ht₀_lt := (hm_max t₀ (Ioo_subset_Icc_self t₀_mem)).eq_or_lt
  · obtain hx₃_lt | hx₃_gt := lt_or_gt_of_ne x₃_neq
    · exact three_preimages hf2 (by grind) (by grind) x₃_mem h_eq rfl
    exact three_preimages hf2 (by grind) (by grind) rfl h_eq x₃_mem
  have ht₀_pos : 0 < f t₀ := hc _ t₀_mem
  obtain hx₃_lt | hx₃_gt := lt_or_gt_of_ne x₃_neq
  · obtain ⟨c, ⟨hc₁, hc₂⟩, hfc⟩ :=
      exists_mem_Ioo_eq_of_zero_left hf1 x₃_mem_Ioo.1 fx₁_zero x₃_mem ht₀_pos ht₀_lt
    obtain ⟨d, ⟨hd₁, hd₂⟩, hfd⟩ :=
      exists_mem_Ioo_eq_of_zero_right hf1 hm₂ rfl fx₂_zero ht₀_pos ht₀_lt
    exact three_preimages hf2 (by grind) (by grind) hfc rfl hfd
  obtain ⟨c, ⟨hc₁, hc₂⟩, hfc⟩ :=
    exists_mem_Ioo_eq_of_zero_left hf1 hm₁ fx₁_zero rfl ht₀_pos ht₀_lt
  obtain ⟨d, ⟨hd₁, hd₂⟩, hfd⟩ :=
    exists_mem_Ioo_eq_of_zero_right hf1 x₃_mem_Ioo.2 x₃_mem fx₂_zero ht₀_pos ht₀_lt
  exact three_preimages hf2 (by grind) (by grind) hfc rfl hfd

NewTheorem lt_or_ge
