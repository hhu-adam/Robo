import Mathlib


/- Revision:

   add some lemmas and exercises preparing the Boss level of BABYLON
   see A: …   and   B: … below
-/



open Nat
/- A:  3 NEW easy ring exercises introducing useful lemmas -/
theorem Robo.add_pow_two (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

theorem Robo.mul_comm (a b : ℕ) : a * b = b * a := by 
  ring

theorem Robo.mul_assoc (a b : ℕ) : a * b * c = a * (b * c) := by 
  ring

/- NEW exercise that uses these lemmas: 
       very similar manipulations needed in boss level of BAYLON -/
example (x a b : ℕ) (hx : x = 2*b) (hy : y = a^2 + a*x + b^2) : y = (a + b)^2 := by
  rw [add_pow_two] -- or ring
  rw [mul_comm 2 a]
  rw [mul_assoc]
  rw [← hx]
  assumption


/- B: preparation for potential new exercise in BABAYLON 
   -- second, longer proof below would fit in well with exercises on Exist here in QUANTUS  -/

example (i : ℕ) (h : Even i): (-1 : ℤ)^i = 1 := by 
  exact Even.neg_one_pow h

example (i : ℕ) (h : Even i): (-1 : ℤ)^i = 1 := by
  -- omega -- fails
  unfold Even at h 
  obtain ⟨r , hr⟩ := h 
  rw [hr] 
  simp
