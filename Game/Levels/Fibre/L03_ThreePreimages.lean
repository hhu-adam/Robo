import Game.Levels.Fibre.L02_SecondElement

World "Fibre"
Level 3

Introduction "Intro Fibre L03"

open Set FullGrind

/-- If every fibre of `f` consists of exactly two points, then three distinct points cannot share the same value. -/
TheoremDoc three_preimages as "three_preimages" in "Fibre"

Statement three_preimages {f : ℝ → ℝ} (hf : ∀ y, (f ⁻¹' {y}).ncard = 2) {a b c y : ℝ}
    (hab : a < b) (hbc : b < c) (ha : f a = y) (hb : f b = y) (hc : f c = y) : False := by
  have hsub : ({a, b, c} : Set ℝ) ⊆ f ⁻¹' {y} := by grind
  have hfin : (f ⁻¹' {y}).Finite := by
    have h : ∃ p q, p ≠ q ∧ f ⁻¹' {y} = {p, q} := Set.ncard_eq_two.mp (hf y)
    obtain ⟨p, q, -, hpq⟩ := h
    rw [hpq]
    simp_log
  have h3 : ({a, b, c} : Set ℝ).ncard = 3 := by
    apply Set.ncard_eq_three.mpr _
    use a, b, c
    grind
  have hle : ({a, b, c} : Set ℝ).ncard ≤ (f ⁻¹' {y}).ncard := by
    apply Set.ncard_le_ncard hsub hfin
  Branch
    grind
  rw [h3, hf y] at hle
  grind

NewTheorem Set.ncard_eq_three Set.ncard_le_ncard

TheoremTab "Fibre"
