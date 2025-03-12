/-
Additional content needed here for Euklid:

   - Nat.exists_prime_and_dvd
   - Nat.not_dvd_of_between_consec_multiples

TODO:  Check whether `specialize` -- currently introduced here in L04 -- is already used earlier
-/

import Mathlib
namespace Nat
alias _root_.Nat.prime_def := prime_def_lt''

/- Prado L01 -/
theorem Robo.prime_two : Prime 2 := by
  decide

/- Prado L02 -/
theorem Robo.dvd_add {a b c : ℕ} (h : a ∣ b) (g : a ∣ c) : a ∣ b + c := by
  obtain ⟨x, h⟩ := h
  obtain ⟨y, g⟩ := g
  use x + y
  rw [h, g]
  ring

/- Prado L03 -/
theorem Robo.even_iff_two_dvd {a : ℕ} : Even a ↔ 2 ∣ a := by
  -- TODO: is there a shorter way?
  unfold Even
  constructor
  · intro h
    obtain ⟨w, hw⟩ := h
    use w
    rw [hw]
    ring
  · intro h
    obtain ⟨w, hw⟩ := h
    use w
    rw [hw]
    ring

/- Prado L04 -/
example (a p : ℕ) (hp : Prime p) (h : 2 ≤ a) (ha : a ∣ p) : a = p := by
  rw [prime_def] at hp
  obtain ⟨hp₁, hp⟩ := hp
  specialize hp a ha
  obtain hp | hp := hp
  · linarith
  · assumption

/- Prado L05 -/
theorem Robo.not_prime_one : ¬ Nat.Prime 1 := by
  decide

/- Prado L06 -/
theorem Robo.prime_dvd_prime_iff_eq {a b : ℕ} (ha : Prime a) (hb : Prime b) :
    a ∣ b ↔ a = b := by
  constructor
  · intro h
    rw [prime_def] at hb
    obtain ⟨_hb_two, hb⟩ := hb
    apply hb at h
    obtain h | h := h
    · have h' := not_prime_one
      rw [← h] at h'
      contradiction
    · assumption
  · intro h
    rw [h]

/- Prado L07 -/
example {a b : ℕ} (ha : 0 < a) (h : a ∣ b) : ∃! (m : ℕ), a * m = b := by
  obtain ⟨w, hw⟩ := h
  use w
  simp
  constructor
  · rw [hw]
  · intro y hy
    rw [hw] at hy
    rw [Nat.mul_left_cancel_iff] at hy -- TODO: _root_.mul_left_cancel_iff takes priority
    · assumption
    · assumption

/- Prado L08 -/
example : ∃! (p : ℕ), Nat.Prime p ∧ Even p := by
  use 2
  simp
  constructor
  · decide
  · intro y h₁ h₂
    rw [even_iff_two_dvd] at h₂
    rw [prime_dvd_prime_iff_eq] at h₂
    · symm
      assumption
    · decide
    · assumption
