import Mathlib


/- Revision:  add some lemmas and exercises preparing the Boss level of BABYLON
   A: basic ring lemmas, see L02a, L02b, L02c and L03b  (+4)
   B: Even.neg_pow & Odd.neg_pow, see L09a and L09b     (+2)
   C: delete a few levels that become unnecessary       (-4)

   :(  This will take total number of levels up to 14!

   PLAN:  Create new Ring planet, using picture of Orange planet (Saturn)
          and move 5 levels introducing ring & rw to that other planet!

   :)  Then Quantus will be down to 9 levels, which seems much better.
-/



open Nat

/- B: preparation for potential new exercise in BABAYLON
   -- second, longer proof below would fit in well with exercises on Exist here in QUANTUS  -/

/- Quantus L01 -/
example : Nonempty ℕ := by
  use 0

/- Quantus L06: Exists, obtain from Nonempty -/
example (A : Type) (h : Nonempty A) : ∃ a : A, a = a := by
  obtain ⟨a⟩ := h
  use a

/- Quantus L07: Even & decide -/
example : Even 42 := by
  decide

/- Quantus L08: choose & use -/
theorem Robo.Nat.even_square (n : ℕ) (h : Even n) : Even (n ^ 2) := by  -- CHECK whether name is needed
  unfold Even at *
  choose s hs using h
  use 2 * s ^ 2
  rw [hs]
  ring


/- Quantus L09a: Even.neg_pow & Odd.neg_pow  -- needed in BABYLON -/
-- easy variation 1:
example (i : ℕ) (h : Odd i): (-1 : ℤ)^i  + 1 = 0 := by
  rw [Odd.neg_pow]
  ring
  assumption

/- variation 2:
example (i : ℕ) (h : Even i): (-1 : ℤ)^i  + 1 = 2 := by
  rw [Even.neg_pow]
  ring
  assumption
-/

/- Quantus L09b: not_even_iff_odd -- previously introduced in L12 -/
example (i : ℕ): (-1 : ℤ)^i  + (-1 : ℤ)^(i+1) = 0 := by
  by_cases h : Even i
  · rw [Even.neg_pow]
    rw [Odd.neg_pow]
    ring
    · obtain ⟨r, hr⟩ := h
      use r
      rw [hr]
      ring
    · assumption
  · rw [← not_even_iff_odd] at h    -- previously introduced in L12; needs a hint here in any case
    rw [Odd.neg_pow]
    rw [Even.neg_pow]
    ring
    · obtain ⟨r, hr⟩ := h
      use r+1
      rw [hr]
      ring
    · assumption



/- Quantus L10: Forall -/
example : ∀ (x : ℕ), (Even x) → Odd (1 + x) := by
  intro x h
  unfold Even at h
  unfold Odd
  choose y hy using h
  use y
  rw [hy]
  ring

/- Quantus L11: push_neg -/
example {X : Type} (P : X → Prop) :
    ¬ (∃ x : X, P x) ↔ ∀ x : X, ¬ P x := by
  push_neg
  rfl

/- Quantus L12: not_odd_iff_even;  DELETE -/
example : ¬ ∃ (n : ℕ), ∀ (k : ℕ) , Odd (n + k) := by
  push_neg
  intro n
  use n
  rw [← not_odd_iff_even]
  unfold Even
  use n

/- Quantus L13: Drinker's paradox -/
--open Function
example {People : Type} [h_nonempty : Nonempty People] (isDrinking : People → Prop) :
    ∃ (x : People), isDrinking x → ∀ (y : People), isDrinking y := by
  by_cases h : ∀ y, isDrinking y
  · obtain ⟨someone⟩ := h_nonempty
    use someone
    intro
    assumption
  · push_neg at h
    choose p hp using h
    use p
    intro hp'
    contradiction


/- ------------------------------------ -/
/- obsolete levels (removed from game): -/

/- Quantus O04: -/
example (a b : ℕ) (h : a = b) (g : a + a ^ 2 = b + 1) : b + b ^ 2 = b + 1 := by
  rw [h] at g
  assumption

/- Quantus O05: -/
example (x y z : ℕ) (h : x = 2 * y + 1) (g : z = 3 * y + 1): x ^ 2 = 4 * y ^ 2 + z + y := by
  rw [h, g]
  ring

/- Quantus O09: Odd; repeat choose & use -/
example (n : ℕ) (h : Odd n) : Odd (n ^ 2) := by
  choose r hr using h
  use 2 * (r + r ^ 2)
  rw [hr]
  ring

/- Quantus: norm_num -- was needed in BABYLON; now DECIDED AGAINST -/
example (i : ℕ) (h : Odd i): (-1 : ℤ)^i = -1 := by
  -- omega -- fails
  obtain ⟨r , hr⟩ := h
  rw [hr]
  -- simp -- fails (though would work with Even in place of Odd)
  -- omega -- fails
  norm_num

/- Quantus: second execrise with norm_num; now DECIDED AGAINST -/
/- ideally, would like to see an application of norm_num that's a bit different -/
example (k : ℕ) (z : ℤ) (hk: Odd k) : (-z)^k = -z^k := by
  have : (-z)^k = (-1)^k*z^k := by ring
  rw [this]
  obtain ⟨i, hi⟩ := hk
  rw [hi]
  -- simp -- fails (though would work with Even in place of Odd)
  norm_num
