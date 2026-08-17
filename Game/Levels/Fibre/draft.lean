import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Set.Card

open Function Set

lemma ncard_eq_two_lt {s : Set ℝ} :
  s.ncard = 2 ↔ (∃ x y, x < y ∧ s = {x, y}) := by
  rw [ncard_eq_two]
  constructor
  · intro ⟨x, y, hx1, hx2⟩
    by_cases h : x < y
    · use x, y
    · use y, x
      grind
  grind

lemma my_not_two_set {S : Set ℝ} [hSf : Finite S] {x₁ x₂ x₃ : ℝ} (h1 : x₁ ∈ S) (h2 : x₂ ∈ S)
    (h3 : x₃ ∈ S) (h12: x₁ < x₂) (h23: x₂ < x₃) : ncard S ≠ 2 := by
  intro hS
  have h_lt : 2 < S.ncard := by
    rw [two_lt_ncard]
    exact ⟨x₁, h1, x₂, h2, x₃, h3, ne_of_lt h12, ne_of_lt (h12.trans h23), ne_of_lt h23⟩
  grind

lemma my_second_element {A : Type} {S : Set A} {a : A} (h : ncard S = 2) (ha : a ∈ S) :
    ∃ b ∈ S, b ≠ a := by
  rw [ncard_eq_two] at h
  obtain ⟨x, y, neq, S_eq⟩ := h
  simp [S_eq]
  grind

lemma getPreimage {f : ℝ → ℝ} (hf1 : Continuous f) :
    ∀ a b, a < b → ∀ y, y ∈ Set.uIcc (f a) (f b) → f a ≠ y → f b ≠ y →
      ∃ c, a < c ∧ c < b ∧ f c = y := by
  intro a b hab y hy fa fb
  obtain ⟨c, hc, hcy⟩ := intermediate_value_uIcc (f := f) hf1.continuousOn hy
  rw [Set.uIcc_of_le hab.le, Set.mem_Icc] at hc
  grind

lemma cross {f : ℝ → ℝ} (hf1 : Continuous f) (a b c : ℝ) (hab : a < b) :
    (f a = 0 ∧ f b = f c) ∨ (f a = f c ∧ f b = 0) →
      ∀ y, 0 < y → y < f c → ∃ c, a < c ∧ c < b ∧ f c = y := by
  intro hval y hy0 hyM
  refine getPreimage hf1 a b hab y ?_ ?_ ?_
  <;> grind [Set.mem_uIcc]

lemma three_preimages {f : ℝ → ℝ} (hf2 : ∀ y, ncard (f⁻¹' {y}) = 2) {a b c y : ℝ} :
    a < b → b < c → f a = y → f b = y → f c = y → False := by
  intro hab hbc fa fb fc
  have hsub : ({a, b, c} : Set ℝ) ⊆ f ⁻¹' {y} := by grind
  have hfin : (f ⁻¹' {y}).Finite := by
    obtain ⟨p, q, -, hPQ⟩ := Set.ncard_eq_two.mp (hf2 y)
    simp [hPQ]
  have h3 : ({a, b, c} : Set ℝ).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨a, b, c, hab.ne, (hab.trans hbc).ne, hbc.ne, rfl⟩
  have hle := Set.ncard_le_ncard hsub hfin
  rw [h3, hf2 y] at hle
  grind

lemma exist_nonneg {f : ℝ → ℝ} (hf1 : Continuous f) (hf2 : ∀ y, ncard (f⁻¹' {y}) = 2) {x₁ x₂ : ℝ}
    (hx_lt : x₁ < x₂) (hx : f ⁻¹' {0} = {x₁, x₂}) : ∃ x ∈ Ioo x₁ x₂, f x ≤ 0 := by
  by_contra! hc
  have h_max : ∃ x ∈ Icc x₁ x₂, IsMaxOn f (Icc x₁ x₂) x := by
    apply IsCompact.exists_isMaxOn isCompact_Icc (nonempty_Icc.mpr (le_of_lt hx_lt))
    exact Continuous.continuousOn hf1
  obtain ⟨xmax, h_max, h_max_at_xmax⟩ := h_max
  rw [isMaxOn_iff] at h_max_at_xmax
  /- `f x₁ = 0` and `f x₂ = 0`. -/
  have fx₁_zero : f x₁ = 0 := by
    have : x₁ ∈ f ⁻¹' {0} := by simp [hx]
    simpa using this
  have fx₂_zero : f x₂ = 0 := by
    have : x₂ ∈ f ⁻¹' {0} := by simp [hx]
    simpa using this
  have hmid_pos : 0 < f ((x₁ + x₂) / 2):= by
    -- Here can be directly proved by `grind`, but I think it is better to do it using apply hc
    apply hc
    grind
  have hMpos : 0 < f xmax := by grind
  have xmax_Ioo : x₁ < xmax ∧ xmax < x₂ := by grind
  have : xmax ∈ f⁻¹' {f xmax} := by rfl
  /- Here: `x₃` is another preimage of `f xmax`. -/
  obtain ⟨x₃, x₃_mem, x₃_neq⟩ := my_second_element (hf2 _) this
  /- Here: `y₀` is a half of the "peak" `f xmax`. -/
  let y₀ := f xmax / 2
  have y₀_pos : 0 < y₀ := by grind
  have y₀_lt : y₀ < f xmax := by grind
  obtain ⟨a, ha₁, ha₂, hfa⟩ := cross hf1 x₁ _ _ xmax_Ioo.1 (Or.inl ⟨fx₁_zero, rfl⟩) y₀ y₀_pos y₀_lt
  obtain ⟨b, hb₁, hb₂, hfb⟩ := cross hf1 _ x₂ _ xmax_Ioo.2 (Or.inr ⟨rfl, fx₂_zero⟩) y₀ y₀_pos y₀_lt
  /- case 1: `x₃ < x₁`. -/
  by_cases h_lt : x₃ < x₁
  · /- a third preimage of `y₀` lies in `(x₃, x₁)`, left of `a`. -/
    obtain ⟨c, hc1, hc2, hfc⟩ := cross hf1 x₃ x₁ _ h_lt (Or.inr ⟨x₃_mem, fx₁_zero⟩) y₀ y₀_pos y₀_lt
    exact three_preimages hf2 (by linarith) (by linarith) hfc hfa hfb
  /- case 1: `x₂ < x₃`. -/
  by_cases h_gt : x₂ < x₃
  · /- a third preimage of `y₀` lies in `(x₂, x₃)`, left of `b`. -/
    obtain ⟨c, hc1, hc2, hfc⟩ := cross hf1 x₂ x₃ _ h_gt (Or.inl ⟨fx₂_zero, x₃_mem⟩) y₀ y₀_pos y₀_lt
    exact three_preimages hf2 (by linarith) (by linarith) hfa hfb hfc
  /- the rest case: `x₃` inside the interval `[x₁, x₂]`. -/
  let t₀ := (x₃ + xmax) / 2
  have t₀_mem : t₀ ∈ Ioo x₁ x₂ := by grind
  have t₀_mem' : x₁ < t₀ ∧ t₀ < x₂ := t₀_mem
  have x₃_mem_Ioo : x₃ ∈ Ioo x₁ x₂ := by grind
  by_cases h_ft₀ : f t₀ = f xmax
  · by_cases x₃_lt : x₃ < xmax
    · refine three_preimages hf2 ?_ ?_  x₃_mem h_ft₀ rfl
      grind
      grind
    refine three_preimages hf2 ?_ ?_  rfl h_ft₀ x₃_mem
    <;> grind
  have ft₀_lt : f t₀ < f xmax := by grind
    -- lt_of_le_of_ne (h_max_at_xmax t₀ t₀_mem) h_ft₀
  have ht₀pos : 0 < f t₀ := hc _ t₀_mem
  by_cases x₃_lt : x₃ < xmax
  · obtain ⟨c, hc1, hc2, hfc⟩ :=
    cross hf1 _ _ _ x₃_mem_Ioo.1 (Or.inl ⟨fx₁_zero, x₃_mem⟩) (f t₀) ht₀pos ft₀_lt
    obtain ⟨d, hd1, hd2, hfd⟩ :=
      cross hf1 _ _ _ xmax_Ioo.2 (Or.inr ⟨rfl, fx₂_zero⟩) (f t₀) ht₀pos ft₀_lt
    refine three_preimages hf2 ?_ ?_ hfc rfl hfd
    grind
    grind
  have x₃_gt : xmax < x₃ := by grind
  obtain ⟨c, hc1, hc2, hfc⟩ :=
    cross hf1 _ _ _ xmax_Ioo.1 (Or.inl ⟨fx₁_zero, rfl⟩) (f t₀) ht₀pos ft₀_lt
  obtain ⟨d, hd1, hd2, hfd⟩ :=
    cross hf1 _ _ _ x₃_mem_Ioo.2 (Or.inr ⟨x₃_mem, fx₂_zero⟩) (f t₀) ht₀pos ft₀_lt
  refine three_preimages hf2 ?_ ?_ hfc rfl hfd
  grind
  grind

lemma exist_nonpos {f : ℝ → ℝ} (hf1 : Continuous f) (hf2 : ∀ y, ncard (f⁻¹' {y}) = 2) {x₁ x₂ : ℝ}
    (hx_lt : x₁ < x₂) (hx : f ⁻¹' {0} = {x₁, x₂}) : ∃ x ∈ Ioo x₁ x₂, f x ≥ 0 := by
  /- this follows directly from `exist_nonneg` applied to `-f`. -/
  have hf2' : ∀ y, ncard ((-f) ⁻¹' {y}) = 2 := by
    intro y
    have : (-f) ⁻¹' {y} = f ⁻¹' {-y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Pi.neg_apply, neg_eq_iff_eq_neg]
    simpa [this] using hf2 _
  have hx' : (-f) ⁻¹' {0} = {x₁, x₂} := by
    have : (-f) ⁻¹' {0} = f ⁻¹' {0} := by
      ext x
      simp [Set.mem_preimage, Set.mem_singleton_iff, Pi.neg_apply]
    rw [this]; exact hx
  obtain ⟨x, hx_mem, hx_le⟩ := exist_nonneg (continuous_neg_iff.mpr hf1) hf2' hx_lt hx'
  exact ⟨x, hx_mem, by simpa using hx_le⟩

lemma main_theorem : ¬ ∃ (f : ℝ → ℝ), Continuous f ∧ ∀ y, ncard (f⁻¹' {y}) = 2 := by
  intro ⟨f, hf₁, hf₂⟩
  obtain h₀ := hf₂ 0
  obtain ⟨x₁, x₂, hx, hx_eq⟩ := ncard_eq_two_lt.mp h₀
  have fx₁_zero : f x₁ = 0 := by
    have : x₁ ∈ f ⁻¹' {0} := by simp [hx_eq]
    simpa using this
  have fx₂_zero : f x₂ = 0 := by
    have : x₂ ∈ f ⁻¹' {0} := by simp [hx_eq]
    simpa using this
  /- there is a nonnegative element `c`. -/
  obtain ⟨c, ⟨hc1, hc2⟩, hc_nonneg⟩ := exist_nonneg hf₁ hf₂ hx hx_eq
  by_cases hc₀ : f c = 0
  · exact three_preimages hf₂ hc1 hc2 fx₁_zero hc₀ fx₂_zero
  have fc_neg : f c < 0 := lt_of_le_of_ne hc_nonneg hc₀
  /- there is a nonpositive element `d`. -/
  obtain ⟨d, ⟨hd1, hd2⟩, hc_nonpos⟩ := exist_nonpos hf₁ hf₂ hx hx_eq
  by_cases! hd₀ : f d = 0
  · exact three_preimages hf₂ hd1 hd2 fx₁_zero hd₀ fx₂_zero
  have fd_pos : 0 < f d := lt_of_le_of_ne hc_nonpos hd₀.symm
  /- here use intermediate value lemma to find a element with image zero. -/
  -- `f c < 0 < f d` with `c, d ∈ Ioo x₁ x₂`, so `f` vanishes at some `e` between them,
  -- hence inside `Ioo x₁ x₂`. That makes `e` a third preimage of `0`, contradiction.
  have h0_mem : 0 ∈ Set.uIcc (f c) (f d) :=
    Set.mem_uIcc.mpr (Or.inl ⟨fc_neg.le, fd_pos.le⟩)
  obtain ⟨e, he_mem, he_eq⟩ := intermediate_value_uIcc hf₁.continuousOn h0_mem
  rw [Set.mem_uIcc] at he_mem
  have he_Ioo : x₁ < e ∧ e < x₂ := by grind
  exact three_preimages hf₂ he_Ioo.1 he_Ioo.2 fx₁_zero he_eq fx₂_zero
