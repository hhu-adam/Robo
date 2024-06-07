import Game.Metadata.Coersion
import Mathlib

open BigOperators

-- test
example (f : Fin n → ℤ): ∑ i : Fin n, f i = ∑ i : Fin n, f i := by rfl


-- set_option pp.notation false

example (h : d = 0) [NeZero n] : ∑ i : Fin n, ∑ j : Fin n, (if i = j then 1 else d) = ∑ i : Fin n, ∑ j : Fin n, (if i = j then 1 else 0) := by
  congr
  ext i
  congr
  ext j
  by_cases h : i = j
  · rw [if_pos h, if_pos h]
    -- assumption
  · rw [if_neg h, if_neg h]
    assumption
  done
