import Mathlib

/-
   Revision:
   - introduce omega
   - integrate lt_trichotomy into story
   - provide some preliminary exercises to manipulations need in BABYLON exercise on sum_subset,
   - freely use the language of Sets & Finsets

   Currenty 9 levels.

   Story:  Ritha ist verliebt in Omega (nicht im Bild), Lina rollt die Augen, Robo ist eifersüchtig.
-/


/- Luna 01: REMOVE -/
/-
example (n m : ℕ) : m < n ↔ m + 1 ≤ n := by
    rfl
-/

/- Luna 02: can be solved with omega!  -/
/- NOT USED ANYWHERE, so does not need a name -/
theorem Robo.Nat.pos_iff_ne_zero (n : ℕ) : 0 < n ↔ n ≠ 0 := by
  omega
  /- existing solution:
  obtain ⟨⟩ := n       /- only used in ROBOTSWANA L10, and explained here
                        can always be replaced with induction at the expense of an extra line -/
  simp
  constructor
  intro
  simp
  intro
  apply Nat.succ_pos   -- NOT USED ANYWHERE
  -/

/- NEW: linarith -- DECIDED AGAINST  -/
/-
example (x : ℝ) : 0 < x →  x ≠ 0 := by
  intro h
  linarith
-/

/- Luna 03: REMOVE -/
/-
example (n : ℕ) (h : 2 ≤ n) : n ≠ 0 := by
  linarith
-/

/- Luna 03a: lt_trichomoty 1 -/
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


/- Luna 03b: omega (this kind of statement needed in BABYLON for sum_subset exercise) -/
example (l m n x : ℕ) (h₁ : l ≤ m) (h₂ : m ≤ n) : l ≤ x ∧ x ≤ n → ¬ (m ≤ x ∧ x ≤ n) → x ≤ m := by
  omega

/- Luna 03c: linarith version of previous exercise -/
example (l m n x : ℝ) (h₁ : l ≤ m) (h₂ : m ≤ n) : l ≤ x ∧ x ≤ n → ¬ (m ≤ x ∧ x ≤ n) → x ≤ m := by
  intro hn hx
  simp at *
  --linarith (config := {splitNe := true, splitHypotheses := true}) -- fails
  rw [imp_iff_or_not] at hx
  --linarith (config := {splitNe := true, splitHypotheses := true}) -- fails
  obtain hx | hx := hx
  · linarith
  · linarith

/- Luna 03d:
   Icc   (already briefly introduced in Piazza)
   Finset.insert_Icc_eq_Icc_add_one_right  (needed in BABYLON)  -/
namespace Finset
theorem Robo.Finset.insert_Icc_eq_Icc_add_one_right {a b : ℕ} (h : a ≤ b + 1) :
  insert (b+1) (Icc a b) = Icc a (b+1) := by
  ext x
  simp
  omega
end Finset


/- Luna 04: linarith can do non-trivial things -/
example (x y : ℚ) (h₂ : 35/11 * y ≤ 35/2 - 22/21 * x) (h₃ : 8/9 * y ≤ x + 17/8) : y ≤ 34/7 := by
  linarith

/- Luna 05: REMOVE -/
/-
example {A : Prop} (x y : ℤ) (h₁ : x ≤ y → A) (h₂ : y < x → A) : A := by
  obtain h | h | h := lt_trichotomy x y
  · apply h₁
    linarith
  · apply h₁
    linarith
  · apply h₂
    linarith
-/


/- Luna 05a:  Preparation for exercise in BABYLON -/
/-       (This kind of statement needed in BABYLON for sum_subset exercise) -/
/- variation 1:
example (n : ℕ) : n ≤ 5 → n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by
  omega
-/
-- variation 2:
namespace Finset
example (n x : ℕ) (h : 3 ≤ n): x ∈ Icc 0 n \ Icc 3 n → x = 0 ∨ x = 1 ∨ x = 2 := by
  intro h
  simp at h
  omega
end Finset

-- variation 3, still in ℕ,
-- more natural statement but less revelant for BABYLON
/-
namespace Finset
example (l m n : ℕ) (h₁ : l ≤ m) (h₂ : m ≤ n) : Icc l n \ Icc m n  ⊆ Icc l m := by
  --rw [subset_iff]
  intro x hx
  simp at *
  omega
end Finset
-/

-- variation 4, now in ℝ
-- most natural statement, but much more difficult, and not at all revelant for BABYLON
/-
namespace Set
example (l m n : ℝ) (h₁ : l ≤ m) (h₂ : m ≤ n) : Icc l n \ Icc m n  ⊆ Icc l m := by
  --simp [subset_def]
  -- intro x hlx hxn h
  intro x hx
  simp at *
  obtain ⟨ hlx, hxn ⟩ := hx
  rw [imp_iff_or_not] at hxn
  obtain hx | hx := hxn
  · linarith
  · -- linarith (config := {splitNe := true, splitHypotheses := true}) -- fails here!
    constructor
    · linarith
    · linarith
end Set
-/

/- Luna 06: lt_trichotomy 2 -/
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

/- Luna 07: Icc_subset_Icc_iff
   This is the Finset version needed in BABYLON,
   which is much easier to solve because omega is more powerful than linarith -/
namespace Finset
theorem Robo.Finset.Icc_subset_Icc_iff (a₁ b₁ a₂ b₂ : ℕ) (h₁ : a₁ ≤ b₁) :
  Icc a₁ b₁ ⊆ Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ := by
  -- unfold Icc -- optional
  simp [subset_iff]
  -- omega -- still fails here
  constructor
  · -- omega -- still fails here
    intro h
    have h' := h
    specialize h h₁
    have : a₁ ≤ a₁ := by rfl
    specialize h' this
    omega
  · omega
end Finset


/- NOTE:  We need all three of

          linarith
          omega
          decide
-/

namespace Nat
example : Prime 2 := by
  decide
  -- omega -- fails

example : Even 2 := by
  decide
  -- omega -- fails

example (n : ℕ) : n < 3 ↔ n = 0 ∨ n = 1 ∨ n = 2 := by
  -- decide -- fails
  -- linarith -- fails
  omega
