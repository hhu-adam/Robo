import Game.Metadata.Tactic.Simp
import Mathlib.Algebra.MvPolynomial.CommRing

-- success with standard simp:
#guard_msgs in
example (I : Finset ℕ) : (∑ i ∈ I, 1) = Finset.card I := by simp (config := {})

-- failure with custom simp before registring any `game_simp` lemmas:
/-- error -/
#guard_msgs (error, substring := true) in
example (I : Finset ℕ) : (∑ i ∈ I, 1) = Finset.card I := by simp

-- success with costum simp after registering relevant `game_simp` lemmas:
attribute [game_simp] Finset.sum_const smul_eq_mul mul_one
#guard_msgs in
example (I : Finset ℕ) : (∑ i ∈ I, 1) = Finset.card I := by simp
