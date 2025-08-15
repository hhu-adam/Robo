/-
  There's potential to introduce `specialize` and `generalize` on this planet.
  `specialize` is currently introduced on Prado, en passant.
  `generalize` would be useful on `Piazza`, in a context that would fit well here:
  -/

import Mathlib
open Nat Real

-- good application of `generalize`:

example (n : ℕ) : Even n ∨ Odd n := by
  rw [not_even_iff_odd]
  generalize Even n = A
  tauto

-- I cannot find a good easy example of a worthwhile application of `specialize`.
-- Usually, if `specialize` works, so does `apply`.
-- Here's my best attempt so far:

example (a b c: ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (habc : a*b*c = 0) (h : ∀ (x y z: ℝ), x ≠ 0  ∧ z ≠ 0 → (x*y*z = 0 ↔ y = 0)) : b = 0 := by
  -- Cannot simply use   `apply h`; “output” of `h` needs to be used here with `rw`.
  -- Cannot directly use `apply h a b c at …` because `a ≠ 0` and `c ≠ 0` are given as separate hypotheses.
  specialize h a b c ⟨ha, hc⟩ -- but specialize statament also needs `⟨ , ⟩` syntax here!
  rw [← h]
  assumption
