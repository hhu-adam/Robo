import Mathlib

/- linarith versus omega (versus decide) -/

namespace Nat 
open Real Set

-- Following example works both for 
--   ℝ and Set.Icc and for
--   ℕ and Finset.Icc:
example (x n : ℝ) (h : 3 ≤ n): x ∈ Icc 0 n → x ∉ Icc 3 n → x ≤ 3 := by
  --linarith -- fails
  intro hn hx
  simp at *
  -- linarith -- fails
  rw [imp_iff_or_not] at hx
  -- linarith -- fails
  obtain hx | hx := hx
  linarith  
  linarith

-- For ℕ and Finset.Icc, omega is shorter:
example (x n : ℕ) : x ∈ Finset.Icc 0 n → x ∉ Finset.Icc 3 n → x ≤ 3 := by
  -- omega fails
  intro hn hx
  simp at *
  omega

-- But decide can do things omega cannot do:
open Finset
example : Prime 2 := by
  decide
  -- omega -- fails

example : Even 2 := by
  decide
  -- omega -- fails

example (n : ℕ) : n < 3 ↔ n = 0 ∨ n = 1 ∨ n = 2 := by
  -- decide -- fails
  omega 
  
