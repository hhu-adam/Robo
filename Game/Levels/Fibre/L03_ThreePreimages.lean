import Game.Levels.Fibre.L02_SecondElement

World "Fibre"
Level 3

Introduction "Intro Fibre L03"

open Set FullGrind

Statement three_preimages {f : ℝ → ℝ} (hf : ∀ y, (f ⁻¹' {y}).ncard = 2) {a b c y : ℝ}
    (hab : a < b) (hbc : b < c) (ha : f a = y) (hb : f b = y) (hc : f c = y) : False := by
  have hsub : ({a, b, c} : Set ℝ) ⊆ f ⁻¹' {y} := by grind
  have hfin : (f ⁻¹' {y}).Finite := by
    obtain ⟨p, q, -, hpq⟩ := Set.ncard_eq_two.mp (hf y)
    rw [hpq]
    apply Set.toFinite
  have h3 : ({a, b, c} : Set ℝ).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨a, b, c, hab.ne, (hab.trans hbc).ne, hbc.ne, rfl⟩
  have hle := Set.ncard_le_ncard hsub hfin
  rw [h3, hf y] at hle
  grind

NewTheorem Set.ncard_eq_three Set.ncard_le_ncard Set.toFinite
