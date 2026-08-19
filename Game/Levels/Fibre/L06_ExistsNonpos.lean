import Game.Levels.Fibre.L05_MaxInIoo

World "Fibre"
Level 6

Introduction "Intro Fibre L06"

open Set FullGrind

/-- Somewhere strictly between the two zeros of `f` the value of `f` is at most `0`. -/
TheoremDoc exists_mem_Ioo_val_nonpos as "exists_mem_Ioo_val_nonpos" in "Fibre"

Statement exists_mem_Ioo_val_nonpos {f : ℝ → ℝ} (hf1 : Continuous f)
    (hf2 : ∀ y, (f ⁻¹' {y}).ncard = 2) {x₁ x₂ : ℝ} (hx_lt : x₁ < x₂)
    (hx : f ⁻¹' {0} = {x₁, x₂}) : ∃ x ∈ Ioo x₁ x₂, f x ≤ 0 := by
  Hint "[Hint k9vtb] **The mathematical idea.**

  Argue by contradiction: assume `f` is strictly positive everywhere strictly between its two
  zeros `x₁` and `x₂`.

  On the compact interval `Icc x₁ x₂` the function attains a maximum, at some point `m`.  As f
  vanishes at both endpoints but is positive in between, m lies strictly inside, and the peak
  value `f m` is positive.

  Now look at half the peak, `y₀ = f m / 2`.  Climbing from x₁ up to m the function passes
  through `y₀`, and descending from m to x₂ it passes through y₀ a second time.  Two preimages
  of y₀, then — and a third one is already forbidden.  Producing that third one is the whole
  game.

  It comes from the second preimage `x₃` of the peak value f m, which exists because every
  value is taken exactly twice:

  * if x₃ lies left of x₁, or right of x₂, then f runs from f m down to `0` along that outer
    stretch and crosses y₀ once more;
  * otherwise x₃ sits inside, and we compare the values at x₃, at m, and at the midpoint `t₀`
    between them.  Either `f t₀` equals the peak — making x₃, t₀ and m three preimages of f m —
    or `0 < f t₀` and f t₀ is smaller than the peak, and then f t₀ is attained on both sides of
    the peak as well as at t₀ itself."
  by_contra! hc
  have h_ends : f x₁ = 0 ∧ f x₂ = 0 := val_eq_of_preimage_eq_pair hx
  obtain ⟨fx₁_zero, fx₂_zero⟩ := h_ends
  have h_max : ∃ x ∈ Icc x₁ x₂, IsMaxOn f (Icc x₁ x₂) x := exists_isMaxOn_Icc hf1 hx_lt.le
  obtain ⟨m, hm_mem, hm_max⟩ := h_max
  have h_inside : m ∈ Ioo x₁ x₂ ∧ 0 < f m :=
    max_mem_Ioo hx_lt fx₁_zero fx₂_zero hc hm_mem hm_max
  obtain ⟨hm_Ioo, hm_pos⟩ := h_inside
  obtain ⟨hm₁, hm₂⟩ := hm_Ioo
  rw [isMaxOn_iff] at hm_max
  have hself : m ∈ f ⁻¹' {f m} := rfl
  have h_second : ∃ b ∈ f ⁻¹' {f m}, b ≠ m := exists_second_mem (hf2 _) hself
  obtain ⟨x₃, x₃_mem, x₃_neq⟩ := h_second
  let y₀ := f m / 2
  have y₀_pos : 0 < y₀ := by grind
  have y₀_lt : y₀ < f m := by grind
  have h_a : ∃ c ∈ Ioo x₁ m, f c = y₀ :=
    exists_mem_Ioo_eq_of_zero_left hf1 hm₁ fx₁_zero rfl y₀_pos y₀_lt
  obtain ⟨a, ⟨ha₁, ha₂⟩, hfa⟩ := h_a
  have h_b : ∃ c ∈ Ioo m x₂, f c = y₀ :=
    exists_mem_Ioo_eq_of_zero_right hf1 hm₂ rfl fx₂_zero y₀_pos y₀_lt
  obtain ⟨b, ⟨hb₁, hb₂⟩, hfb⟩ := h_b
  /- case 1: `x₃` lies left of `x₁` -/
  have hcases₁ : x₃ < x₁ ∨ x₁ ≤ x₃ := lt_or_ge x₃ x₁
  obtain h_lt | h_ge := hcases₁
  · have h_c : ∃ c ∈ Ioo x₃ x₁, f c = y₀ :=
      exists_mem_Ioo_eq_of_zero_right hf1 h_lt x₃_mem fx₁_zero y₀_pos y₀_lt
    obtain ⟨c, ⟨hc₁, hc₂⟩, hfc⟩ := h_c
    apply three_preimages hf2 _ _ hfc hfa hfb
    · grind
    · grind
  /- case 2: `x₃` lies right of `x₂` -/
  have hcases₂ : x₂ < x₃ ∨ x₃ ≤ x₂ := lt_or_ge x₂ x₃
  obtain h_gt | h_le := hcases₂
  · have h_c : ∃ c ∈ Ioo x₂ x₃, f c = y₀ :=
      exists_mem_Ioo_eq_of_zero_left hf1 h_gt fx₂_zero x₃_mem y₀_pos y₀_lt
    obtain ⟨c, ⟨hc₁, hc₂⟩, hfc⟩ := h_c
    apply three_preimages hf2 _ _ hfa hfb hfc
    · grind
    · grind
  /- case 3: `x₃` lies inside `Ioo x₁ x₂` -/
  have x₃_mem_Ioo : x₃ ∈ Ioo x₁ x₂ := by grind
  let t₀ := (x₃ + m) / 2
  have t₀_mem : t₀ ∈ Ioo x₁ x₂ := by grind
  have hcases₃ : f t₀ = f m ∨ f t₀ < f m := (hm_max t₀ (Ioo_subset_Icc_self t₀_mem)).eq_or_lt
  obtain h_eq | ht₀_lt := hcases₃
  · have hcases₄ : x₃ < m ∨ x₃ > m := lt_or_gt_of_ne x₃_neq
    obtain hx₃_lt | hx₃_gt := hcases₄
    · apply three_preimages hf2 _ _ x₃_mem h_eq rfl
      · grind
      · grind
    apply three_preimages hf2 _ _ rfl h_eq x₃_mem
    · grind
    · grind
  have ht₀_pos : 0 < f t₀ := hc _ t₀_mem
  have hcases₅ : x₃ < m ∨ x₃ > m := lt_or_gt_of_ne x₃_neq
  obtain hx₃_lt | hx₃_gt := hcases₅
  · have h_c : ∃ c ∈ Ioo x₁ x₃, f c = f t₀ :=
      exists_mem_Ioo_eq_of_zero_left hf1 x₃_mem_Ioo.1 fx₁_zero x₃_mem ht₀_pos ht₀_lt
    obtain ⟨c, ⟨hc₁, hc₂⟩, hfc⟩ := h_c
    have h_d : ∃ d ∈ Ioo m x₂, f d = f t₀ :=
      exists_mem_Ioo_eq_of_zero_right hf1 hm₂ rfl fx₂_zero ht₀_pos ht₀_lt
    obtain ⟨d, ⟨hd₁, hd₂⟩, hfd⟩ := h_d
    apply three_preimages hf2 _ _ hfc rfl hfd
    · grind
    · grind
  have h_c : ∃ c ∈ Ioo x₁ m, f c = f t₀ :=
    exists_mem_Ioo_eq_of_zero_left hf1 hm₁ fx₁_zero rfl ht₀_pos ht₀_lt
  obtain ⟨c, ⟨hc₁, hc₂⟩, hfc⟩ := h_c
  have h_d : ∃ d ∈ Ioo x₃ x₂, f d = f t₀ :=
    exists_mem_Ioo_eq_of_zero_right hf1 x₃_mem_Ioo.2 x₃_mem fx₂_zero ht₀_pos ht₀_lt
  obtain ⟨d, ⟨hd₁, hd₂⟩, hfd⟩ := h_d
  apply three_preimages hf2 _ _ hfc rfl hfd
  · grind
  · grind

NewTheorem lt_or_ge

TheoremTab "Fibre"
