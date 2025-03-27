import Mathlib

/- RING 01  -/
theorem Robo.add_pow_two (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

/- RING 02 -/
theorem Robo.mul_comm (a b : ℕ) : a * b = b * a := by
  ring

/- RING 03 -/
theorem Robo.mul_assoc (a b c: ℕ) : a * b * c = a * (b * c) := by
  ring

/- RING 04: rewrite equalities -/
example (a b c d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = c := by
  rw [h₁]
  rw [←h₂]
  assumption

/- RING 05: -/
namespace MvPolynomial
example (A B :  MvPolynomial (Fin 4) ℝ) (hA : A = (X 0)*(X 3) - (X 1)*(X 2)) (hB : B = (X 0)*(X 2) + (X 1)*(X 3)) :
  ((X 0)^2 + (X 1)^2) * ((X 2)^2 + (X 3)^2) = A^2 + B^2  := by
  rw [hA, hB]
  ring


/- Further ideas

Introduce more interesting arithemetic in ℝ?
Tactic `ring` does not handle devision (`/`) or inversion (`⁻¹`) well.
Instead, would need to use `field_simp`, eg:
-/
open Real
example (x p q : ℝ) (hx : x = -p/2 + sqrt (p^2/4 - q)) (hdisc: p^2/4 - q ≥ 0): x^2 + p*x + q = 0 := by
  rw [hx]
  rw [add_pow_two,sq_sqrt]
  field_simp
  ring
  assumption
