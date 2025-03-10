import Mathlib

/-
   Revision:
   - introduce omega
   - integrate lt_trichotomy into story
   - provide some preliminary exercises to manipulations need in BABYLON exercise on sum_subset
-/


/- Luna 01: REMOVE -/
example (n m : ℕ) : m < n ↔ m + 1 ≤ n := by
    rfl

/- Luna 02: can be solved with omega!  -/
theorem Robo.Nat.pos_iff_ne_zero (n : ℕ) : 0 < n ↔ n ≠ 0 := by  -- CHECK whether this is used anywhere
  omega
  /- existing solution:
  obtain ⟨⟩ := n       -- CHECK whether this is used anywhere
  simp
  constructor
  intro
  simp
  intro
  apply Nat.succ_pos   -- CHECK whether this is used anywhere
  -/

/- Luna NEW: linarith-/
example (x : ℝ) : 0 < x →  x ≠ 0 := by
  intro h
  linarith

/- Luna 03: REMOVE -/
example (n : ℕ) (h : 2 ≤ n) : n ≠ 0 := by
  linarith

/- Luna NEW: omega (this kind of statement needed in BABYLON for sum_subset exercise) -/
example (m n : ℕ) (h₁ : l ≤ m) (h₂ : m ≤ n) : l ≤ x ∧ x ≤ n → ¬ (m ≤ x ∧ x ≤ n) → x ≤ m := by
  omega 

/- Luna NEW: linarith version of previous exercise (repeat in PIAZZA) -/
example (m n : ℝ) (h₁ : l ≤ m) (h₂ : m ≤ n) : l ≤ x ∧ x ≤ n → ¬ (m ≤ x ∧ x ≤ n) → x ≤ m := by
  intro hn hx
  simp at *
  --linarith (config := {splitNe := true, splitHypotheses := true}) -- fails 
  rw [imp_iff_or_not] at hx
  --linarith (config := {splitNe := true, splitHypotheses := true}) -- fails 
  obtain hx | hx := hx
  · linarith 
  · linarith 

/- Luna 04: linarith can do non-trivial things -/
example (x y : ℤ) (h₂ : 5 * y ≤ 35 - 2 * x) (h₃ : 2 * y ≤ x + 3) : y ≤ 5 := by
  linarith

/- Luna 05: REMOVE -/
example {A : Prop} (x y : ℤ) (h₁ : x ≤ y → A) (h₂ : y < x → A) : A := by
  obtain h | h | h := lt_trichotomy x y
  · apply h₁
    linarith
  · apply h₁
    linarith
  · apply h₂
    linarith

/- Luna NEW:  omega, again (this kind of statement needed in BABYLON for sum_subset exercise) -/
example (n : ℕ) : n ≤ 5 → n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by
  omega

/- Luna NEW: lt_trichomoty 1 -/
theorem Robo.lt_trichotomy (a b c : ℝ): a < b ∨ a = b ∨ b < a := by
  by_cases h_leq : a ≤ b
  · by_cases h_lt : a < b
    · left
      assumption -- or linarith
    · right
      left
      linarith  -- WANT LINARITH in this exercise!
  · right
    right
    linarith -- WANT LINARITH in this exercise!

/- Luna NEW: lt_trichotomy 2-/
example (a c : ℝ) (h : a ≠ c): ∃ b : ℝ, a < b ∧ b < c ∨ c < b ∧ b < a := by
  use (a + c) / 2 
  obtain h | h | h := lt_trichotomy a c 
  · left 
    constructor
    all_goals linarith
  · contradiction
  · right
    constructor
    all_goals linarith
