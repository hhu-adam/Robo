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

/- RING 05: preparation for very similar manipulation needed in boss level of BABYLON -/
example (w a o : ℤ) (h2o : 2*o = 100) (ho2 : o^2 = -100*a - a^2) (h :  w = (a + o)^2) : w = 0 := by
  rw [add_pow_two] at h
  rw [mul_comm 2 a] at h
  rw [mul_assoc] at h
  rw [h2o] at h
  rw [ho2] at h
  rw [h]
  ring
