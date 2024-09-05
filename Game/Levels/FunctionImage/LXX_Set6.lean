import Game.Metadata

open Set

-- DELETE?

example (f : ℝ → ℝ) (hfib : ncard (f ⁻¹' {0}) = 2) : ∃ (x₁ x₂ : ℝ ), x₁ ≠ x₂ ∧ f x₁ = 0 ∧ f x₂ = 0 := by
  apply ncard_eq_two.mp at hfib
  obtain ⟨ x₁, x₂, h_ne, h_fib_eq ⟩ := hfib
  use x₁, x₂
  constructor
  assumption
  change x₁ ∈ f ⁻¹' {0} ∧ x₂ ∈ f ⁻¹' {0}
  rw [h_fib_eq]
  tauto
