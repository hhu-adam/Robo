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

/- RING 01 / Quantus L02: ADD NAME, this is used in BABYLON -/
theorem Robo.add_pow_two (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

/- RING 02 / Quantus L02b: NEW -/
theorem Robo.mul_comm (a b : ℕ) : a * b = b * a := by
  ring

/- RING 03 / Quantus L02c: NEW -/
theorem Robo.mul_assoc (a b c: ℕ) : a * b * c = a * (b * c) := by
  ring

/- RING 04 / Quantus L03: rewrite -/
example (a b c d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = c := by
  rw [h₁]
  rw [←h₂]
  assumption

/- RING 05 / Quantus L03b: NEW exercise that trains rewrite and uses above lemmas;
                 very similar manipulations needed in boss level of BAYLON -/
example (x y a b : ℕ) (hx : x = 2*b) (hy : y = a^2 + a*x + b^2) : y = (a + b)^2 := by
  rw [add_pow_two] -- or ring
  rw [mul_comm 2 a]
  rw [mul_assoc]
  rw [← hx]
  assumption

/- Quantus L04: NOT NEEDED ANYMORE -/
example (a b : ℕ) (h : a = b) (g : a + a ^ 2 = b + 1) : b + b ^ 2 = b + 1 := by
  rw [h] at g
  assumption

/- Quantus L05: NOT NEEDED ANYMORE -/
example (x y z : ℕ) (h : x = 2 * y + 1) (g : z = 3 * y + 1): x ^ 2 = 4 * y ^ 2 + z + y := by
  rw [h, g]
  ring

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

/- Quantus L09: Odd; repeat choose & use -- NOW SUPERFLUOUS  -/
example (n : ℕ) (h : Odd n) : Odd (n ^ 2) := by
  choose r hr using h
  use 2 * (r + r ^ 2)
  rw [hr]
  ring

/- Quantus: norm_num -- was needed in BABYLON; now DECIDED AGAINST -/
/- example (i : ℕ) (h : Odd i): (-1 : ℤ)^i = -1 := by
  -- omega -- fails
  obtain ⟨r , hr⟩ := h
  rw [hr]
  -- simp -- fails (though would work with Even in place of Odd)
  -- omega -- fails
  norm_num
-/

/- Quantus: second execrise with norm_num; now DECIDED AGAINST -/
/- ideally, would like to see an application of norm_num that's a bit different -/
/-example (k : ℕ) (z : ℤ) (hk: Odd k) : (-z)^k = -z^k := by
  have : (-z)^k = (-1)^k*z^k := by ring
  rw [this]
  obtain ⟨i, hi⟩ := hk
  rw [hi]
  -- simp -- fails (though would work with Even in place of Odd)
  norm_num
-/

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

/- Quantus L09b: odd_iff_not_even -- previously introduced in L12 -/
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
  · rw [← odd_iff_not_even] at h    -- previously introduced in L12; needs a hint here in any case
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

/- Quantus L12: even_iff_not_odd;  DELETE -/
example : ¬ ∃ (n : ℕ), ∀ (k : ℕ) , Odd (n + k) := by
  push_neg
  intro n
  use n
  rw [← even_iff_not_odd]
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
