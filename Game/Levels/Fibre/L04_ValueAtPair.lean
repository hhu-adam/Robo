import Game.Levels.Fibre.L03_ThreePreimages

World "Fibre"
Level 4

Introduction "Intro Fibre L04"

open Set FullGrind

/-- If the fibre over `y` is the pair `{x₁, x₂}`, then `f` takes the value `y` at both of these points. -/
TheoremDoc val_eq_of_preimage_eq_pair as "val_eq_of_preimage_eq_pair" in "Fibre"

Statement val_eq_of_preimage_eq_pair {f : ℝ → ℝ} {y x₁ x₂ : ℝ} (hx : f ⁻¹' {y} = {x₁, x₂}) :
    f x₁ = y ∧ f x₂ = y := by
  constructor
  · have h : x₁ ∈ f ⁻¹' {y} := by
      rw [hx]
      simp
    simpa using h
  · have h : x₂ ∈ f ⁻¹' {y} := by
      rw [hx]
      simp
    simpa using h

TheoremTab "Fibre"
